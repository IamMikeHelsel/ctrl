#!/usr/bin/env python3
"""Create a small local source/evidence package; do not publish or upload it."""
from pathlib import Path
import hashlib
import io
import json
import tarfile

WORKSPACE = Path(__file__).resolve().parents[1]
PUBLICATION = WORKSPACE/'publication'
PROJECT = WORKSPACE/'lean-controls'


def sha(blob):
    return hashlib.sha256(blob).hexdigest()


def main():
    verified = json.loads((PROJECT/'evidence/project-verification.json').read_text())
    if verified['status'] != 'verified':
        raise RuntimeError('Project verification has not passed.')
    for relative, expected in verified['source_sha256'].items():
        if sha((PROJECT/relative).read_bytes()) != expected:
            raise RuntimeError(f'Stale project evidence: {relative}')

    replay = json.loads((PUBLICATION/'application-fresh-replay.json').read_text())
    if replay['status'] != 'passed':
        raise RuntimeError('Independent application source replay has not passed.')
    for relative, expected in replay['original_source_sha256_before'].items():
        if sha((PROJECT/relative).read_bytes()) != expected:
            raise RuntimeError(f'Stale independent replay evidence: {relative}')

    paper = json.loads((PUBLICATION/'manuscript-compilation.json').read_text())
    if paper['status'] != 'success' or not paper['pdf_exported']:
        raise RuntimeError('Checked paper PDF has not been exported.')
    for path_key, hash_key in [('source','source_sha256'),('output','output_sha256'),
                               ('supporting_figure','supporting_figure_sha256')]:
        if sha((PUBLICATION/paper[path_key]).read_bytes()) != paper[hash_key]:
            raise RuntimeError(f'Stale paper evidence: {paper[path_key]}')
    comparison = json.loads((PUBLICATION/'application-comparison/verification.json').read_text())
    if comparison['status'] != 'verified':
        raise RuntimeError('Matched SOS replay is not verified.')
    if sha((PUBLICATION/'application-comparison/TravelSOSReplay.lean').read_bytes()) != comparison['source_sha256']:
        raise RuntimeError('Stale SOS source evidence.')

    selected = set()
    for name in ['.gitignore','LeanControls.lean','Audit.lean','lean-toolchain','lakefile.toml',
                 'lake-manifest.json','check.sh','requirements.txt','README.txt']:
        selected.add(PROJECT/name)
    for directory, patterns in [('LeanControls',['*.lean','*.json']),
                                ('benchmarks',['*.json']),('scripts',['*.py']),
                                ('evidence',['*.json','*.log'])]:
        for pattern in patterns:
            selected.update((PROJECT/directory).rglob(pattern))
    for pattern in ['*.txt','*.json','*.log','*.html','*.py']:
        selected.update(PUBLICATION.glob(pattern))
    selected.update((PUBLICATION/'manuscript').glob('*.tex'))
    selected.add(PUBLICATION/'manuscript/main.pdf')
    for directory in [WORKSPACE/'research/application', PUBLICATION/'application-comparison']:
        for pattern in ['*.txt','*.json','*.log','*.lean','*.py']:
            selected.update(directory.glob(pattern))
    # Include the curated, separate prize-screening aid, not downloaded papers,
    # web-page copies, or third-party research checkouts.
    for name in ['shortlist.html','erdos-catalog.html','erdos-manifest.json',
                 'erdos-manifest.csv','erdos-counts.json','erdos-provenance.json',
                 'erdos-LICENSE','catalog-sources.txt','catalog-review.txt',
                 'erdos-preliminary-candidates.txt','controls-awards.txt','hager-screen.txt',
                 'build_catalog.py','other-prize-sources.json']:
        selected.add(WORKSPACE/'research/prize-problems'/name)
    for pattern in ['*.pdf','*.png']:
        selected.update((PUBLICATION/'manuscript/images').glob(pattern))
    for pattern in ['*.txt','*.json','*.log']:
        selected.update((WORKSPACE/'research/travel-limit').glob(pattern))
    for pattern in ['*.txt','*.json','*.log','*.lean','*.py']:
        selected.update((PUBLICATION/'comparison').glob(pattern))
    for name in ['rank-four-core.txt','mf13-next-step.txt','orthogonal-notes.txt',
                 'certificate-design.txt']:
        selected.add(WORKSPACE/'research'/name)
    for name in ['saturated-entry.txt','double-integrator-bridge.txt',
                 'sampling-clock.txt','model-semantics.txt']:
        selected.add(WORKSPACE/'research/publication'/name)

    # Freeze bytes before constructing the archive. Do not include compiler
    # products, caches, external checkouts, toolchains, or nested source archives.
    blobs = {}
    for path in sorted(selected):
        if path.is_symlink():
            raise RuntimeError(f'Refusing a selected symlink: {path}')
        if path.is_file():
            blobs[str(path.relative_to(WORKSPACE))] = path.read_bytes()
    manifest = {'status':'local source snapshot, not a publication',
                'project_verified_declarations':verified['audited_public_declarations'],
                'proof_evidence':'lean-controls/evidence/project-verification.json',
                'fresh_replay':'publication/application-fresh-replay.json',
                'files':{name:{'sha256':sha(blob),'bytes':len(blob)} for name,blob in blobs.items()}}
    blobs['MANIFEST.json'] = (json.dumps(manifest,indent=2)+'\n').encode()
    target = PUBLICATION/'lean-controls-application-2026-10-17.tar.gz'
    if target.exists():
        raise RuntimeError('Refusing to replace an existing frozen source package.')
    with tarfile.open(target,'w:gz') as archive:
        for name,blob in blobs.items():
            info = tarfile.TarInfo('lean-controls-research/'+name)
            info.size = len(blob)
            info.mode = 0o755 if name.endswith('check.sh') else 0o644
            info.mtime = 0
            archive.addfile(info,io.BytesIO(blob))
    # Read back every file and compare bytes, not just the table of contents.
    with tarfile.open(target,'r:gz') as archive:
        members = archive.getmembers()
        if len(members) != len(blobs):
            raise RuntimeError('Archive member count mismatch.')
        for member in members:
            name = member.name.removeprefix('lean-controls-research/')
            if archive.extractfile(member).read() != blobs[name]:
                raise RuntimeError(f'Archive readback mismatch: {name}')
    checksum = sha(target.read_bytes())
    target.with_suffix('.sha256').write_text(checksum+'  '+target.name+'\n')
    print(json.dumps({'archive':str(target),'files':len(blobs),'bytes':target.stat().st_size,
                      'sha256':checksum,'readback':'all file bytes matched'},indent=2))


if __name__ == '__main__':
    main()

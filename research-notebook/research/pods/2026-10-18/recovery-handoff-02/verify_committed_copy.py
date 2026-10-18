#!/usr/bin/env python3
"""Check each notebook manifest digest against an actual committed Git blob."""
import argparse
import hashlib
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--ref', default='HEAD')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    repo = args.repo.resolve()
    commit = subprocess.check_output(
        ['git', 'rev-parse', '--verify', args.ref + '^{commit}'], cwd=repo, text=True).strip()
    manifest_path = 'research-notebook/_sync/manifest.json'
    manifest_bytes = subprocess.check_output(['git', 'show', commit + ':' + manifest_path], cwd=repo)
    if manifest_bytes != (repo / manifest_path).read_bytes():
        raise ValueError('Committed sync manifest differs from the checked working copy')
    manifest = json.loads(manifest_bytes)
    proc = subprocess.Popen(['git', 'cat-file', '--batch'], cwd=repo,
                            stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    total_bytes = 0
    try:
        for name, entry in manifest['files'].items():
            if '\n' in name or '\r' in name:
                raise ValueError('Unsupported newline in manifest path')
            proc.stdin.write((commit + ':research-notebook/' + name + '\n').encode())
            proc.stdin.flush()
            header = proc.stdout.readline().decode().strip().split()
            if len(header) != 3 or header[1] != 'blob':
                raise ValueError('Missing committed blob: ' + name)
            size = int(header[2])
            data = proc.stdout.read(size)
            if proc.stdout.read(1) != b'\n' or len(data) != size:
                raise ValueError('Truncated Git object response: ' + name)
            if hashlib.sha256(data).hexdigest() != entry['sha256'] or size != entry['bytes']:
                raise ValueError('Committed blob differs from recorded source: ' + name)
            total_bytes += size
        proc.stdin.close()
        if proc.wait() != 0:
            raise ValueError('Git object reader failed')
    finally:
        if proc.poll() is None:
            proc.terminate()
            proc.wait()
    report = {'utc': datetime.now(timezone.utc).isoformat(), 'passed': True,
              'commit': commit, 'files_verified': len(manifest['files']),
              'bytes_verified': total_bytes,
              'manifest_sha256': hashlib.sha256(manifest_bytes).hexdigest(),
              'scope': 'Committed blob identity only; proof acceptance and remote delivery are separate.'}
    text = json.dumps(report, indent=2) + '\n'
    if args.output:
        if args.output.exists():
            raise ValueError('Use a new output path; recorded checks are not overwritten')
        args.output.write_text(text)
    print(text)


if __name__ == '__main__':
    main()

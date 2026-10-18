#!/usr/bin/env python3
"""Fail-closed inventory and copied-input validation; independent of Lean execution."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import sys

class InventoryError(RuntimeError):
    pass

def require(condition, message):
    if not condition:
        raise InventoryError(message)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read_sums(path):
    result = {}
    for line in path.read_text().splitlines():
        h, name = line.split(None, 1)
        name = name.lstrip('*')
        require(name not in result, 'Duplicate checksum entry: '+name)
        result[name] = h
    return result

def check_inventory(bundle, run=None, complete=False):
    bundle = Path(bundle).resolve()
    spec_path = bundle/'verification-inventory.json'
    spec = json.loads(spec_path.read_text())
    folders = ['source', 'accepted', 'controls', 'accepted-controls']
    require(spec['directories'] == folders, 'Unexpected inventory directories')
    expected = spec['files']
    require(len(expected) == 70, 'Expected exactly 70 frozen proof-critical files')
    actual = set()
    for folder in folders:
        root = bundle/folder
        require(root.is_dir(), 'Missing directory: '+folder)
        for p in root.rglob('*'):
            require(not p.is_symlink(), 'Symlink input: '+str(p))
            if p.is_dir():
                continue
            require(p.is_file() and not p.is_symlink(), 'Non-regular input: '+str(p))
            actual.add(p.relative_to(bundle).as_posix())
    require(actual == set(expected),
            'Inventory mismatch; missing='+str(sorted(set(expected)-actual))+
            '; extra='+str(sorted(actual-set(expected))))
    required_counts = {'source':25, 'accepted':13, 'controls':13, 'accepted-controls':19}
    for folder, n in required_counts.items():
        require(sum(p.split('/')[0] == folder for p in expected) == n,
                'Wrong frozen file count: '+folder)
    for relative, h in expected.items():
        require(re.fullmatch(r'[0-9a-f]{64}', h) is not None, 'Invalid digest: '+relative)
        require(digest(bundle/relative) == h, 'Hash mismatch: '+relative)
    # Bind baseline controls to the previously accepted critic manifest, not a
    # newly blessed version of whatever happens to be in controls/.
    for relative, h in spec['provenance_hashes'].items():
        require(digest(bundle/relative) == h, 'Provenance hash mismatch: '+relative)
    critic = read_sums(bundle/'provenance/critic-05-SHA256SUMS')
    builder = read_sums(bundle/'provenance/builder-05-SHA256SUMS')
    for relative, h in expected.items():
        if relative.startswith('controls/'):
            require(critic.get('clients/'+Path(relative).name) == h,
                    'Baseline critic provenance mismatch: '+relative)
        if relative.startswith('source/'):
            require(builder.get(Path(relative).name) == h,
                    'Baseline builder provenance mismatch: '+relative)
    mathematical = sorted(Path(p).stem for p in expected
                          if p.startswith(('source/', 'accepted/')) and p.endswith('.lean'))
    reviewers = sorted(['ReviewerClient','CounterWitnesses'] +
                       [Path(p).stem for p in expected if p.startswith('accepted-controls/')
                        and p.endswith('.lean')])
    negatives = sorted(p for p in expected if p.endswith('.lean.txt'))
    require(len(mathematical)==38 and len(set(mathematical))==38, 'Wrong mathematical module set')
    require(len(reviewers)==10 and len(set(reviewers))==10, 'Wrong reviewer module set')
    require(len(negatives)==20, 'Wrong false-client set')
    require(sorted(spec['mathematical_modules'])==mathematical, 'Manifest mathematical-module mismatch')
    require(sorted(spec['reviewer_modules'])==reviewers, 'Manifest reviewer-module mismatch')
    require(sorted(spec['false_clients'])==negatives, 'Manifest false-client mismatch')
    positives = mathematical + reviewers
    require(len(set(positives))==48, 'Colliding positive module names')
    positive_paths = {Path(p).stem:p for p in expected
                      if p.endswith('.lean') and Path(p).stem in positives}
    require(len(positive_paths)==48, 'Ambiguous positive module paths')
    result = {'status':'PASS','bundle':str(bundle),'manifest_sha256':digest(spec_path),
              'frozen_files':70,'mathematical_modules':38,'reviewer_modules':10,
              'false_clients':20,'baseline_control_provenance':'13 hashes match accepted critic-05 manifest',
              'python_optimization':sys.flags.optimize,'complete':bool(complete)}
    if run is not None:
        run = Path(run).resolve()
        require(run.is_dir(), 'Missing replay directory: '+str(run))
        expected_run = {m+'.lean':expected[p] for m,p in positive_paths.items()}
        negative_run = {Path(p).name.removesuffix('.txt'):expected[p] for p in negatives}
        require(len(negative_run)==20, 'Colliding false-client names')
        copied = list(run.glob('*.lean'))
        require(all(p.is_file() and not p.is_symlink() for p in copied), 'Non-regular copied Lean source')
        observed = {p.name for p in copied}
        allowed = set(expected_run) | set(negative_run) | {'FinalAudit.lean'}
        require(not observed-allowed, 'Unexpected copied Lean source: '+str(sorted(observed-allowed)))
        require(set(expected_run)<=observed, 'Missing copied positive source: '+str(sorted(set(expected_run)-observed)))
        for name,h in expected_run.items():
            require(digest(run/name)==h, 'Copied-source hash mismatch: '+name)
        for name,h in negative_run.items():
            if name in observed:
                require(digest(run/name)==h, 'Copied false-client hash mismatch: '+name)
        if complete:
            require(set(negative_run)<=observed, 'Missing copied false control: '+str(sorted(set(negative_run)-observed)))
            require('FinalAudit.lean' in observed, 'Missing generated audit')
        if 'FinalAudit.lean' in observed:
            generated = (run/'FinalAudit.lean').read_text()
            imports = re.findall(r'^import\s+(\S+)\s*$', generated, re.M)
            order = [m for m in imports if m != 'Lean.Util.CollectAxioms']
            require(len(order)==48 and set(order)==set(positives), 'Generated audit import coverage mismatch')
            template = (bundle/'controls/FinalAudit.lean').read_text()
            expected_audit = template.replace('import CounterWitnesses','\n'.join('import '+m for m in order))
            expected_audit,n = re.subn(r'let owned : Array Name := #\[[^\]]*\]',
                         'let owned : Array Name := #['+', '.join('`'+m for m in order)+']', expected_audit)
            require(n==1, 'Ambiguous frozen audit template')
            require(generated==expected_audit, 'Generated audit differs from frozen template or ownership coverage')
        result.update(run=str(run),copied_positive_sources=48,
                      copied_false_sources=len(observed & set(negative_run)),
                      generated_audit_checked='FinalAudit.lean' in observed)
    else:
        require(not complete, '--complete requires --run')
    return result

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--bundle',type=Path,default=Path(__file__).resolve().parent)
    p.add_argument('--run',type=Path)
    p.add_argument('--complete',action='store_true')
    p.add_argument('--output',type=Path)
    a=p.parse_args()
    try:
        result=check_inventory(a.bundle,a.run,a.complete)
    except (InventoryError,OSError,ValueError,KeyError,TypeError) as e:
        result={'status':'FAIL','error':str(e),'python_optimization':sys.flags.optimize}
        code=1
    else:
        code=0
    rendered=json.dumps(result,indent=2)+'\n'
    if a.output:
        a.output.write_text(rendered)
    print(rendered,end='')
    return code

if __name__=='__main__':
    raise SystemExit(main())

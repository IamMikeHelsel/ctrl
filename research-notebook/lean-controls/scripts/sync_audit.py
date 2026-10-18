#!/usr/bin/env python3
"""Inventory this project's named public theorem declarations and module imports.

This is deliberately a small source-inventory tool, not a Lean parser or proof
checker. The generated Audit.lean is checked by Lean; its output is checked by
check_audit.py. Private helper proofs are covered transitively by that audit.
Run with --check to reject stale inventories without changing files.
"""
import argparse
import json
from pathlib import Path
import re

PROJECT = Path(__file__).resolve().parents[1]


def without_comments(source):
    # Nested block comments are used by Lean. Retain newlines for locations.
    depth = 0
    i = 0
    result = []
    while i < len(source):
        if source[i:i+2] == '/-':
            depth += 1
            result.extend('  ')
            i += 2
        elif depth and source[i:i+2] == '-/':
            depth -= 1
            result.extend('  ')
            i += 2
        elif not depth and source[i:i+2] == '--':
            end = source.find('\n', i)
            if end < 0:
                break
            result.extend(' ' * (end-i))
            i = end
        else:
            result.append(source[i] if not depth or source[i] == '\n' else ' ')
            i += 1
    if depth:
        raise ValueError('Unclosed Lean block comment')
    return ''.join(result)


def inventory():
    records = []
    modules = []
    for path in sorted((PROJECT/'LeanControls').rglob('*.lean')):
        relative = path.relative_to(PROJECT)
        modules.append('.'.join(relative.with_suffix('').parts))
        namespaces = []
        for line, text in enumerate(without_comments(path.read_text()).splitlines(), 1):
            if match := re.match(r'^namespace (\S+)\s*$', text):
                namespaces.append(match[1])
            elif match := re.match(r'^end (\S+)\s*$', text):
                if not namespaces or namespaces[-1] != match[1]:
                    raise ValueError(f'{relative}:{line}: unsupported or mismatched scope')
                namespaces.pop()
            elif match := re.match(r'^(?:public )?(?:theorem|lemma) (\S+)', text):
                name = match[1]
                if not re.fullmatch(r'[\w\u0080-\uffff]+', name):
                    raise ValueError(f'{relative}:{line}: unsupported declaration name {name}')
                records.append({'name':'.'.join(namespaces+[name]),
                                'source':str(relative),'line':line})
        if namespaces:
            raise ValueError(f'{relative}: unclosed namespace')
    if len({r['name'] for r in records}) != len(records):
        raise ValueError('Duplicate qualified declaration names')
    return modules, records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    modules, records = inventory()
    files = {
        'LeanControls.lean': 'module\n\n' + ''.join('public import '+m+'\n' for m in modules),
        'Audit.lean': 'import LeanControls\n\n' + ''.join('#print axioms '+r['name']+'\n' for r in records),
        'evidence/declarations.json': json.dumps(records, indent=2)+'\n',
    }
    for filename, content in files.items():
        path = PROJECT/filename
        if args.check:
            if not path.exists() or path.read_text() != content:
                raise SystemExit(f'Stale {filename}; run python3 scripts/sync_audit.py')
        else:
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_text(content)
    print(f'{len(modules)} modules; {len(records)} named public theorem declarations inventoried.')


if __name__ == '__main__':
    main()

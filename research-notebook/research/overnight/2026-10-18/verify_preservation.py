"""Check explicitly named frozen manifests; do not infer proof acceptance."""
from pathlib import Path
import argparse
import datetime
import hashlib
import importlib.util
import json


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def entries(path):
    if path.suffix == '.json':
        data = json.loads(path.read_text())
        data = data.get('files', data)
        return {name: value['sha256'] if isinstance(value, dict) else value
                for name, value in data.items()}
    result = {}
    for line in path.read_text().splitlines():
        digest, name = line.split(maxsplit=1)
        result[name.lstrip('*')] = digest
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--index', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--source', type=Path, default=Path(__file__).resolve().parents[3])
    parser.add_argument('--destination', type=Path)
    args = parser.parse_args()
    source = args.source.resolve()
    ignored = lambda _: False
    if args.destination:
        tool = args.destination.resolve().parent / 'tools/sync_research_notebook.py'
        spec = importlib.util.spec_from_file_location('notebook_sync', tool)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        ignored = module.ignored
    index = json.loads(args.index.read_text())
    artifacts = []
    seen_manifests = set()
    seen_files = set()
    excluded = set()
    stored = set()
    for item in index['artifacts']:
        manifest = source / item['manifest']
        assert manifest not in seen_manifests, f'duplicate manifest: {manifest}'
        seen_manifests.add(manifest)
        assert sha(manifest) == item['sha256'], f'manifest changed: {manifest}'
        records = entries(manifest)
        for name, expected in records.items():
            local = (manifest.parent / name).resolve()
            relative = local.relative_to(source)
            assert sha(local) == expected, f'frozen source changed: {local}'
            seen_files.add(relative.as_posix())
            if args.destination:
                if ignored(relative):
                    excluded.add(relative.as_posix())
                else:
                    assert sha(args.destination / relative) == expected, f'stored copy differs: {relative}'
                    stored.add(relative.as_posix())
        if args.destination:
            assert sha(args.destination / item['manifest']) == item['sha256']
        artifacts.append({**item, 'entries_verified': len(records)})
    result = {
        'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'passed': True,
        'distinct_manifests': len(seen_manifests),
        'unique_files_verified': len(seen_files),
        'preserved_frozen_files_checked': len(stored) if args.destination else None,
        'excluded_build_files_checked_in_source': len(excluded) if args.destination else None,
        'excluded_paths': sorted(excluded),
        'note': 'Hash preservation does not establish review acceptance or full live-source freshness.',
        'artifacts': artifacts,
    }
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ['artifacts', 'excluded_paths']}))


if __name__ == '__main__':
    main()

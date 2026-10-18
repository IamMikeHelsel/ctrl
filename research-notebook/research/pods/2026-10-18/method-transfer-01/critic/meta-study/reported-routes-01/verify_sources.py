"""Read-only verification of the critic's copied source packet. Prints JSON."""
import hashlib
import json
from pathlib import Path
from pypdf import PdfReader

BASE = Path(__file__).resolve().parent
P = BASE / 'inputs'
ROOT_HASH = '0243f7751a3ee59d947ca00bcec4d34f5eebf5ae4258fcbb0aef415ca8929f40'
REVISION = '1581d4cbdd69a0faf34b2089614fe2a814316a6a'
REVISED_HASH = 'cb1b27b3777d3d061dca1e5619043cc9b188d4a24db3c24a3e37ab91b376885c'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

assert sha(P / 'root-manifest.json') == ROOT_HASH
frozen = json.loads((P / 'root-manifest.json').read_text())['files']
assert len(frozen) == 36
for filename, expected in frozen.items():
    assert sha(P / filename) == expected, filename
assert sha(P / 'READ-ME-REVISED.txt') == REVISED_HASH
root = json.loads((P / 'corpus-root-tree.json').read_text())
tree = json.loads((P / 'corpus-reasoning_traces-tree.json').read_text())
assert root['sha'] == REVISION and not root['truncated'] and not tree['truncated']
assert next(e for e in root['tree'] if e['path'] == 'reasoning_traces')['sha'] == tree['sha']
entries = {e['path']: e for e in tree['tree'] if e['path'].endswith('.pdf')}
sources = json.loads((P / 'source-manifest.json').read_text())
ledger = json.loads((P / 'READING-COVERAGE.json').read_text())
assert sources['revision'] == ledger['source_revision'] == REVISION
assert set(entries) == {s['file'] for s in sources['sources']}
assert len(entries) == 10
records = {s['file']: s for s in ledger['sources']}
out = []
for s in sources['sources']:
    name = s['file']
    raw = (P / name).read_bytes()
    blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
    assert blob == s['git_blob_sha1'] == entries[name]['sha']
    assert len(raw) == s['bytes'] == entries[name]['size']
    assert sha(P / name) == s['sha256'] == records[name]['sha256']
    assert sha(P / (name[:-4] + '.txt')) == s['text_sha256']
    pages = PdfReader(P / name).pages
    stored = json.loads((P / (name[:-4] + '.pages.json')).read_text())
    assert len(pages) == len(stored) == s['pages']
    selected = records[name]['full_pages_read']
    assert selected == sorted(set(selected))
    for n in selected:
        assert pages[n - 1].extract_text() == stored[n - 1], (name, n)
    intro = records[name]['introductory_excerpt']
    if intro:
        assert intro['page'] == 1 and 0 < intro['characters'] <= len(stored[0])
        assert pages[0].extract_text()[:intro['characters']] == stored[0][:intro['characters']]
    out.append({'file': name, 'pages': len(pages), 'selected_pages': selected,
                'introductory_excerpt': intro, 'all_bytes_and_selected_text_match': True})
assert sum(s['pages'] for s in out) == ledger['total_source_pages'] == 202
assert sum(len(s['selected_pages']) for s in out) == ledger['full_pages_read'] == 48
assert sum(len(s['selected_pages']) == s['pages'] for s in out) == 4
assert sum(bool(s['introductory_excerpt']) for s in out) == 6
print(json.dumps({'passed': True, 'root_manifest_sha256': ROOT_HASH,
                  'root_frozen_files': 36, 'revised_readme_sha256': REVISED_HASH,
                  'source_revision': REVISION, 'complete_pdf_inventory': 10,
                  'source_pages': 202, 'selected_full_pages': 48,
                  'complete_selected_summaries': 4, 'introductory_excerpts': 6,
                  'sources': out,
                  'scope': 'Checks bytes, pinned tree membership, extraction and ledger arithmetic; does not verify headline mathematics or prove reading activity.'}, indent=2))

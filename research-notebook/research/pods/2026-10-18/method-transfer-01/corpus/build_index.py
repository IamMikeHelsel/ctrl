"""Inventory the pinned catalogue. Keyword hits are a reading aid, not a verdict."""
from pathlib import Path
from collections import Counter
import json
import re
import hashlib

BASE = Path(__file__).resolve().parent
manifest = json.loads((BASE / 'source-manifest.json').read_text())
for entry in manifest['files']:
    data = (BASE / entry['path']).read_bytes()
    assert hashlib.sha256(data).hexdigest() == entry['sha256']
contents = (BASE / 'CONTENTS.md').read_text()
overview = (BASE / 'overview.tex').read_text()
paths = set()
for filename, prefix in [('preprints-tree.json','preprints/'), ('lean-docs-tree.json','lean/docs/')]:
    tree = json.loads((BASE / filename).read_text())
    assert not tree.get('truncated'), f'Incomplete {filename}'
    paths.update(prefix + x['path'] for x in tree['tree'])
subjects = {}
subject = None
for line in overview.splitlines():
    section = re.match(r'\\cataloguesection\{([^}]+)\}', line)
    if section:
        subject = section[1]
    item = re.match(r'\\resultentry\{(\d{3})\}', line)
    if item:
        assert subject is not None
        assert item[1] not in subjects
        subjects[item[1]] = subject
starts = list(re.finditer(r'^\*\*(\d{3})\. (.+?)\*\*', contents, re.M))
families = []
patterns = {
    'graph_structure': r'triangle|graphon|sparse.half|cut|independent set|spectral|semidefinite|realizab',
    'entropy_probability': r'entrop|coupling|transport|spin.glass|interpolat|concentration|martingale|conditional',
    'controls_analysis': r'control|stabil|dissipat|Lyapunov|optimal|reachab|delay|switch|monoton|comparison|differential inclusion',
    'algebra_geometry': r'Clifford|spinor|invariant|equivarian|representation|gauge|torsion|curvature|Lie algebra|finite.support',
}
for i, m in enumerate(starts):
    block = contents[m.start(): starts[i+1].start() if i+1 < len(starts) else len(contents)]
    papers = re.findall(r'^&emsp;\[(.*?)\]\((preprints/.+?\.pdf)\)', block, re.M)
    links = re.findall(r'\[Lean\]\((lean/[^)]+)\)', block)
    for _, p in papers:
        assert p in paths, p
    for p in links:
        assert p in paths, p
    description = block[len(m[0]):].split('</td>', 1)[0].strip()
    families.append({
        'id':m[1], 'title':m[2].rstrip('.'), 'subject':subjects[m[1]],
        'catalogue_claim':description,
        'papers':[{'title':t,'path':p} for t,p in papers],
        'lean_documentation_paths':links,
        'screening_tags':[k for k,p in patterns.items() if re.search(p, block, re.I)],
        'reading_depth':'metadata only; deeper reviews are separate role records',
    })
assert len(families) == 372, len(families)
assert len(subjects) == 372
assert len({f['id'] for f in families}) == 372
assert {f['id'] for f in families} == set(subjects)
paper_count = sum(len(f['papers']) for f in families)
assert paper_count == 719, paper_count
assert len({p['path'] for f in families for p in f['papers']}) == 719
result = {'revision':manifest['revision'], 'scope':'Complete metadata inventory, not proof validation or deep reading.',
          'families':families}
(BASE/'family-index.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
summary = {'families':len(families), 'manuscripts':paper_count,
           'family_ids_are_contiguous':False,
           'id_range':[min(subjects),max(subjects)],
           'absent_ids_in_range':sorted({f'{n:03}' for n in range(int(min(subjects)),int(max(subjects))+1)}-set(subjects)),
           'families_with_lean_doc_link':sum(bool(f['lean_documentation_paths']) for f in families),
           'subjects':dict(Counter(f['subject'] for f in families)),
           'caution':'A Lean documentation link is not a verified unconditional theorem. Tags are keyword screening, not discovery mechanism classification.'}
(BASE/'inventory-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
lines = ['PINNED CORPUS: COMPLETE METADATA INVENTORY', manifest['revision'], '',
         'All 372 families and 719 manuscript links were parsed and matched to the repository tree.',
         'This is a reading map. Source claims are not endorsed. No corpus proof was replayed.', '',
         'ID | Subject | Family title | Manuscripts | Lean documentation link']
lines += [f"{f['id']} | {f['subject']} | {f['title']} | {len(f['papers'])} | {bool(f['lean_documentation_paths'])}" for f in families]
(BASE/'CORPUS-MAP.txt').write_text('\n'.join(lines)+'\n')
print(json.dumps(summary,indent=2))

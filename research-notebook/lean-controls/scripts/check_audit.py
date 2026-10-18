"""Fail if an audited declaration depends on anything beyond standard axioms."""
import json
import re
from pathlib import Path

text = Path('evidence/axioms.log').read_text()
records = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, re.S)
empty = re.findall(r"'([^']+)' does not depend on any axioms", text)
expected = re.findall(r'^#print axioms (\S+)', Path('Audit.lean').read_text(), re.M)
assert len(records) + len(empty) == len(expected), (len(records), len(empty), len(expected), text)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
result = {}
for name, ax in records:
    axioms = {a.strip() for a in ax.split(',') if a.strip()}
    assert axioms <= allowed, (name, axioms - allowed)
    result[name] = sorted(axioms)
for name in empty:
    result[name] = []
assert set(result) == set(expected)
Path('evidence/axioms.json').write_text(json.dumps(result, indent=2))
print(f'{len(result)} declarations checked; only standard Lean axioms.')

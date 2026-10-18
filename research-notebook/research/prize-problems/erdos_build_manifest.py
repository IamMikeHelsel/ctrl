#!/usr/bin/env python3
"""Build a lossless screening manifest from a pinned community catalog.
Requires PyYAML and jsonschema. Does not retrieve or submit any material.
"""
from pathlib import Path
from collections import Counter
import csv, hashlib, json, re
import yaml
from jsonschema import Draft202012Validator, FormatChecker
HERE = Path(__file__).resolve().parent
class UniqueLoader(yaml.SafeLoader):
    pass
def unique_mapping(loader, node, deep=False):
    out = {}
    for key_node, value_node in node.value:
        key = loader.construct_object(key_node, deep=deep)
        if key in out:
            raise ValueError(f'duplicate YAML key: {key}')
        out[key] = loader.construct_object(value_node, deep=deep)
    return out
UniqueLoader.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, unique_mapping)
provenance = json.loads((HERE/'erdos-provenance.json').read_text())
for file in provenance['files']:
    assert hashlib.sha256((HERE/file['local']).read_bytes()).hexdigest() == file['sha256']
raw = yaml.load((HERE/'erdos-problems.yaml').read_text(), Loader=UniqueLoader)
Draft202012Validator(json.loads((HERE/'erdos-problems.schema.json').read_text()), format_checker=FormatChecker()).validate(raw)
assert len({p['number'] for p in raw}) == len(raw)
official = json.loads((HERE/'erdos-official-prizes.json').read_text())
site = {p['number']:p for p in official['entries']}
assert len(site) == len(official['entries'])
for page in official['pages']:
    assert hashlib.sha256((HERE/page['file']).read_bytes()).hexdigest() == page['sha256']
open_states = {'open','falsifiable','verifiable','decidable'}
rows=[]
for p in raw:
    n=p['number'];prize=p.get('prize');m=re.fullmatch(r'([$£₹])(\d+(?:\.\d+)?)',prize or '')
    state=p.get('informal_status',{}).get('state')
    r={'number':n,'problem_url':f'https://www.erdosproblems.com/{n}',
       'community_prize_raw':prize,'community_prize_listed':None if prize is None else prize!='no',
       'community_prize_currency_symbol':m.group(1) if m else None,
       'community_prize_amount':m.group(2) if m else None,
       'official_display_dollars':site.get(n,{}).get('official_display_dollars'),
       'official_prize_listed':n in site,'prize_payment_verified':None,
       'informal_status':state,'informal_status_last_update':p.get('informal_status',{}).get('last_update'),
       'informal_status_note':p.get('informal_status',{}).get('note'),
       'formal_solution_status':p.get('formal_status',{}).get('state'),
       'formal_solution_url':p.get('formal_status',{}).get('url'),
       'formal_solution_last_update':p.get('formal_status',{}).get('last_update'),
       'formal_solution_note':p.get('formal_status',{}).get('note'),
       'derived_status':p.get('status',{}).get('state'),
       'statement_formalized':p.get('formalized',{}).get('state'),
       'statement_formalized_last_update':p.get('formalized',{}).get('last_update'),
       'statement_url':f'https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/{n}.lean' if p.get('formalized',{}).get('state')=='yes' else None,
       'tags':p.get('tags'),'oeis':p.get('oeis'),'comments':p.get('comments'),
       'ordinary_unresolved_label':state in open_states,
       'raw_community_entry':p}
    rows.append(r)
counts={'entries':len(rows),'unique_numbers':len({r['number'] for r in rows}),
    'all_integer_ids_1_to_1221':{r['number'] for r in rows}=={str(i) for i in range(1,1222)},
    'informal_status':dict(sorted(Counter(r['informal_status'] for r in rows).items())),
    'formal_solution_status':dict(sorted(Counter(r['formal_solution_status'] for r in rows).items())),
    'statement_formalized':dict(sorted(Counter(r['statement_formalized'] for r in rows).items())),
    'community_prize_listed':sum(r['community_prize_listed'] is True for r in rows),
    'official_prize_listed':len(site),
    'community_open_exact_prize':sum(r['informal_status']=='open' and r['community_prize_listed'] is True for r in rows),
    'official_open_exact_prize':sum(r['informal_status']=='open' and r['official_prize_listed'] for r in rows),
    'ordinary_unresolved_labels':sum(r['ordinary_unresolved_label'] for r in rows),
    'ordinary_unresolved_community_prize':sum(r['ordinary_unresolved_label'] and r['community_prize_listed'] is True for r in rows),
    'ordinary_unresolved_official_prize':sum(r['ordinary_unresolved_label'] and r['official_prize_listed'] for r in rows),
    'open_labels_with_formal_solution':[(r['number'],r['derived_status']) for r in rows if r['ordinary_unresolved_label'] and r['formal_solution_status']=='Lean'],
    'official_only_prize_numbers':[r['number'] for r in rows if r['official_prize_listed'] and r['community_prize_listed'] is False],
    'missing_source_fields':{k:sum(k not in p for p in raw) for k in ['number','prize','informal_status','formal_status','status','formalized','oeis','tags','comments']}}
manifest={'scope':'All entries in the pinned current community metadata catalog; not all historical Erdos questions; no completeness claim for statements, solutions or payable prizes.',
 'revision':provenance['revision'],'retrieved_utc':provenance['retrieved_utc'],
 'schema_validation':'Draft202012 plus format checking; duplicate keys and numbers rejected',
 'unknown_policy':'Missing fields are null in JSON and empty cells in CSV; missing is never inferred false. Raw source entries retained in JSON. Prize payment unverified for every entry.',
 'ordinary_unresolved_states':sorted(open_states),'counts':counts,'entries':rows}
(HERE/'erdos-manifest.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n')
fields=[k for k in rows[0] if k!='raw_community_entry']
with (HERE/'erdos-manifest.csv').open('w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=fields);w.writeheader()
    for r in rows:
        w.writerow({k:json.dumps(r[k],ensure_ascii=False) if isinstance(r[k],(list,dict)) else r[k] for k in fields})
(HERE/'erdos-counts.json').write_text(json.dumps(counts,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(counts,ensure_ascii=False,indent=2))

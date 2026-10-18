#!/usr/bin/env python3
"""Prepare a versioned metadata queue. No network or model calls are made."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT.parent / 'prize-problems/erdos-manifest.json'

def main():
    raw = SOURCE.read_bytes()
    catalog = json.loads(raw)
    rows = []
    for entry in sorted(catalog['entries'], key=lambda e: int(e['number'])):
        rows.append({
            'id': 'erdos-' + entry['number'], 'family': 'erdos',
            'title': 'Erdős #' + entry['number'], 'active_budget_seconds': 300,
            'preparation_status': 'needs_pinned_statement_and_current_status_check',
            'attempt_status': 'not_started', 'launchable': False,
            'source_url': entry['problem_url'], 'statement_url': entry['statement_url'],
            'metadata_revision': catalog['revision'],
            'metadata_source_sha256': hashlib.sha256(raw).hexdigest(),
            'informal_status_at_snapshot': entry['informal_status'],
            'formal_solution_label_at_snapshot': entry['formal_solution_status'],
            'ordinary_unresolved_label': entry['ordinary_unresolved_label'],
            'mode': ('research_diagnostic' if entry['ordinary_unresolved_label']
                     else 'calibration_or_status_review'),
            'tags': entry['tags'], 'listed_prize_is_not_verified_payable': True,
            'baseline_result_disclosed_to_model': False,
            'source_inputs': [], 'verification_status': 'not_run',
            'promotion_requires': ['source-faithful statement review',
                                  'independent mathematical review',
                                  'appropriate proof/counterexample checker',
                                  'current literature and priority check'],
        })
    assert len({r['id'] for r in rows}) == len(rows)
    (ROOT/'erdos-queue.jsonl').write_text(''.join(json.dumps(r,ensure_ascii=False)+'\n' for r in rows))
    major_source = ROOT.parent/'opportunity-assessment/big-opportunities-next/task-cards.json'
    major_raw = major_source.read_bytes()
    major = []
    for card in json.loads(major_raw)['tasks']:
        major.append({**card, 'family':'major_opportunity',
                      'active_budget_seconds':300,
                      'preparation_status':'needs_pinned_statement_and_current_status_check',
                      'attempt_status':'not_started', 'launchable':False,
                      'source_inputs':[],
                      'metadata_source_sha256':hashlib.sha256(major_raw).hexdigest(),
                      'prior_development_is_not_a_timed_sweep_result':True})
    (ROOT/'major-opportunities-queue.jsonl').write_text(''.join(json.dumps(r,ensure_ascii=False)+'\n' for r in major))
    summary = {'catalog_revision':catalog['revision'], 'catalog_sha256':hashlib.sha256(raw).hexdigest(),
               'erdos_entries':len(rows), 'active_seconds_per_entry':300,
               'serial_active_hours':len(rows)*300/3600,
               'preparation_and_model_warmup_included_in_active_hours':False,
               'launchable':sum(r['launchable'] for r in rows),
               'attempts_started':0,
               'major_opportunity_cards':len(major),
               'major_opportunity_cards_sha256':hashlib.sha256(major_raw).hexdigest(),
               'combined_serial_active_hours':(len(rows)+len(major))*300/3600,
               'scope':'All entries of the pinned catalog, including solved calibration cases; not all historical Erdős questions.'}
    (ROOT/'queue-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__ == '__main__':
    main()

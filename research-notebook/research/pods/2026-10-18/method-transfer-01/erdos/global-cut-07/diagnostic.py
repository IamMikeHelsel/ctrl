#!/usr/bin/env python3
"""Analyze only the fixed recorded sample; no new graphs or weights."""
from pathlib import Path
from fractions import Fraction as Q
import json
HERE=Path(__file__).resolve().parent
def main():
 d=json.loads((HERE/'screen-results.json').read_text());hosts={h['name']:h for h in d['hosts']};R=Q(1,40);rows=[]
 for z in d['cases']:
  W=z['weight_sum'];a=z['integer_weights'];E=hosts[z['host']]['edges'];n=len(a)
  tough=uniformbad=completionbad=unavailable=0;oldmax=umax=Q(0)
  for t in z['global_orientations']:
   X=t['X_mask'];xm=sum(a[v] for v in range(n) if X>>v&1);ym=W-xm
   q=Q(sum(a[u]*a[v] for u,v in E if X>>u&1 and X>>v&1),W*W)
   j=sum(a[u]*a[v] for u,v in E if not(X>>u&1) and not(X>>v&1))
   U=Q(j,4*ym*ym);x=Q(xm,W)
   C=(3*x*x/2-5*x/4+Q(9,32) if x<=Q(3,8) else x*(Q(1,2)-x)/2)+q if x>=Q(1,3) else None
   old=min(U,C) if C is not None else U
   tough+=old>R;uniformbad+=U>R;completionbad+=C is not None and C>R;unavailable+=C is None
   oldmax=max(oldmax,old);umax=max(umax,U)
  rows.append({'host':z['host'],'pattern':z['weight_pattern'],'best':z['best_global_certificate'],
   'worst':z['worst_global_certificate'],'optimum':z['true_fractional_half']['cost'],
   'ties':z['global_ties_up_to_complement'],'orientations':len(z['global_orientations']),
   'old_bounds_both_fail':tough,'uniform_above_target':uniformbad,'completion_above_target':completionbad,
   'completion_unavailable':unavailable,'largest_old_certificate':str(oldmax),'largest_uniform_cost':str(umax)})
 report={'scope':'Secondary exact analysis of the same fixed sample; no new inputs or trials','cases':rows,
  'total_old_unresolved_orientations':sum(z['old_bounds_both_fail'] for z in rows),
  'total_uniform_above_target':sum(z['uniform_above_target'] for z in rows),
  'total_completion_above_target':sum(z['completion_above_target'] for z in rows),
  'total_completion_unavailable':sum(z['completion_unavailable'] for z in rows),
  'largest_old_certificate':str(max(Q(z['largest_old_certificate']) for z in rows)),
  'largest_uniform_cost':str(max(Q(z['largest_uniform_cost']) for z in rows)),
  'cases_with_best_worst_difference':sum(z['best']!=z['worst'] for z in rows)}
 print(json.dumps(report,indent=2))
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Exact rational jump-TV comparison; no plant run and no tuning."""
from pathlib import Path
from fractions import Fraction as Q
from math import factorial
import json,hashlib
H=Path(__file__).resolve().parent;O=H.parents[1]/'latency-noise-05/builder'
old={(x['case'],x['method']):x['pieces'] for x in json.loads((O/'reference-schedules.json').read_text())['schedules']};oracle=json.loads((H/'native-oracle.json').read_text())
def derivative(p,t,k):
 z=t-Q(p['start_exact']);d=[Q(p[n]) for n in ['p','v','a','jerk','snap']]
 return sum((d[i]*z**(i-k)/factorial(i-k) for i in range(k,5)),Q(0))
def measure(pieces):
 rows=[];full=Q(0);jerkonly=Q(0);joins=Q(0);tiny=[]
 for i,(a,b) in enumerate(zip(pieces,pieces[1:])):
  t=Q(b['start_exact']);assert t==Q(a['end_exact'])
  d=[derivative(b,t,k)-derivative(a,t,k) for k in range(4)]
  correction=800*d[0]+60*d[1]+Q(3,2)*d[2];ju=d[3]/96;du=correction+ju
  full+=abs(du);jerkonly+=abs(ju);joins+=abs(correction)
  rows.append({'time_exact':str(t),'origin_before':a['origin'],'origin_after':b['origin'],'delta_q_v_a_j_exact':[str(x) for x in d],
               'delta_u_exact':str(du),'delta_j_over96_exact':str(ju),'join_correction_exact':str(correction),'delta_u':float(du)})
 for i,p in enumerate(pieces):
  duration=Q(p['end_exact'])-Q(p['start_exact'])
  if duration<Q(1,10**12):tiny.append({'piece_index':i,'origin':p['origin'],'duration_exact':str(duration),'jerk':p['jerk'],'before_jerk':pieces[i-1]['jerk'] if i else None,'after_jerk':pieces[i+1]['jerk'] if i+1<len(pieces) else None})
 return {'full_jump_TV_exact':str(full),'jerk_only_jump_TV_exact':str(jerkonly),'join_correction_TV_bound_exact':str(joins),'full_jump_TV':float(full),'jerk_only_jump_TV':float(jerkonly),'join_correction_TV_bound':float(joins),'events':rows,'tiny_pieces':tiny}
results=[]
for key,v in oracle['streams'].items():
 case,method=key.split('__');a=measure(old[case,method]);b=measure(v['pieces']);full_delta=Q(b['full_jump_TV_exact'])-Q(a['full_jump_TV_exact']);jerk_delta=Q(b['jerk_only_jump_TV_exact'])-Q(a['jerk_only_jump_TV_exact'])
 results.append({'key':key,'old05':a,'new06':b,'new_minus_old_full_jump_TV_exact':str(full_delta),'new_minus_old_full_jump_TV':float(full_delta),'new_minus_old_jerk_only_TV_exact':str(jerk_delta),'new_minus_old_jerk_only_TV':float(jerk_delta),'full_delta_minus_jerk_delta_exact':str(full_delta-jerk_delta),'full_delta_minus_jerk_delta':float(full_delta-jerk_delta)})
result={'units':'command jump total variation in m/s^2; reference jerk in m/s^3; the numerical coefficient 1/96 represents seconds in the declared SI controller','identity':'At fixed actual x,v,a, delta_u=800 delta_q+60 delta_qv+1.5 delta_qa+delta_j/96. Piece duration does not enter the jump contribution abs(delta_u).','interpretation':'This is exact algebra for frozen polynomial pieces. It does not show equal firmware effort or a significant physical motion change. Infinitesimal-duration jerk excursions can retain finite variation.','rows':results}
(H/'jump-variation.json').write_text(json.dumps(result,indent=2)+'\n')
for x in results:print(x['key'],'deltaTV',x['new_minus_old_full_jump_TV'],'jerk-only delta',x['new_minus_old_jerk_only_TV_exact'],'join residual',x['full_delta_minus_jerk_delta'],'tiny',len(x['old05']['tiny_pieces']),len(x['new06']['tiny_pieces']))

#!/usr/bin/env python3
"""Separate exact verifier: Gray-code cut enumeration; no screen import."""
from fractions import Fraction as Q
from pathlib import Path
import json,hashlib,random,copy
HERE=Path(__file__).resolve().parent;R=Q(1,40);I=Q(2,47)
def vertices(s,n):return [v for v in range(n) if s>>v&1]
def adjacency(n,E):
 assert len(E)==len(set(E)) and all(0<=u<v<n for u,v in E),'not simple'
 N=[set() for _ in range(n)]
 for u,v in E:N[u].add(v);N[v].add(u)
 for u,v in E:assert not N[u]&N[v],'triangle violates premise'
 return N
def expected_edges(name,n):
 if name=='Clebsch':
  return sorted({tuple(sorted((v,v^d))) for v in range(16) for d in [1,2,4,8,15]})
 if name=='MycielskiC5':
  def joined(u,v):
   if u<5 and v<5:return (u-v)%5 in [1,4]
   if u<5 and 5<=v<10:return (u-(v-5))%5 in [1,4]
   return 5<=u<10 and v==10
  return [(u,v) for u in range(n) for v in range(u+1,n) if joined(u,v)]
 if name=='Petersen':
  return [(u,v) for u in range(n) for v in range(u+1,n)
          if (v<5 and (u-v)%5 in [1,4]) or (u<5 and v==u+5) or (u>=5 and (u-v)%5 in [2,3])]
 k=int(name[-1]);assert n==3*k-1
 return [(u,v) for u in range(n) for v in range(u+1,n) if abs((3*u)%n-(3*v)%n)%3==1]
def gray_cuts(a,E,N):
 n=len(a);total=[sum(a[u] for u in N[v]) for v in range(n)];selectedN=[0]*n
 cost=sum(a[u]*a[v] for u,v in E);minimum=None;ties=[];local=[];full=(1<<n)-1
 old=0;W=sum(a)
 for k in range(1<<(n-1)):
  s=(k^(k>>1))<<1
  if k:
   changed=s^old;v=changed.bit_length()-1
   same=selectedN[v] if old>>v&1 else total[v]-selectedN[v]
   cost+=a[v]*(total[v]-2*same)
   sign=1 if s>>v&1 else -1
   for u in N[v]:selectedN[u]+=sign*a[v]
  if minimum is None or cost<minimum:minimum=cost;ties=[s]
  elif cost==minimum:ties.append(s)
  if all(2*(selectedN[v] if s>>v&1 else total[v]-selectedN[v])<=total[v] for v in range(n)):
   local.append((s,47*cost<=2*W*W))
  old=s
 assert minimum is not None
 return minimum,sorted(ties),local
def cost(E,p):return sum((p[u]*p[v] for u,v in E),Q(0))
def q_envelope(x):
 assert Q(1,3)<=x<=Q(1,2),'completion domain'
 if x<=Q(3,8):return 3*x*x/2-5*x/4+Q(9,32)
 return x*(Q(1,2)-x)/2
def orientations(s,a):
 n=len(a);full=(1<<n)-1;m=sum(a[v] for v in vertices(s,n));W=sum(a)
 return [s] if 2*m<W else [full^s] if 2*m>W else [s,full^s]
def certificate(a,E,N,X):
 n=len(a);W=sum(a);w=[Q(v,W) for v in a];xs=set(vertices(X,n));ys=set(range(n))-xs
 x=sum((w[v] for v in xs),Q(0));y=1-x;assert x<=y and y>0
 q=cost([(u,v) for u,v in E if u in xs and v in xs],w)
 j=cost([(u,v) for u,v in E if u in ys and v in ys],w)
 p=[w[v]/(2*y) if v in ys else Q(0) for v in range(n)]
 assert sum(p)==Q(1,2);U=cost(E,p);assert U==j/(4*y*y)
 C=q_envelope(x)+q if x>=Q(1,3) else None;rows=[]
 if y>Q(1,2):
  b=y-Q(1,2);d={v:sum((w[u] for u in N[v]&ys),Q(0)) for v in ys}
  for v in sorted(ys):
   nv=N[v]&ys;dv=d[v];sv=sum((w[u]*d[u] for u in nv),Q(0))
   if dv<=b:
    branch='low';p=[w[u]/(2*(y-dv)) if u in ys-nv else Q(0) for u in range(n)]
    f=(j-sv)/(4*(y-dv)**2)
   else:
    branch='high';p=[w[u]*(1-b/dv) if u in nv else w[u] if u in ys else Q(0) for u in range(n)]
    f=j-b*sv/dv
   assert sum(p)==Q(1,2) and all(0<=p[u]<=w[u] for u in range(n)),'invalid profile'
   actual=cost(E,p);assert actual==f,'false neighborhood cost'
   rows.append({'vertex':v,'d':dv,'s':sv,'branch':branch,'predicted':f,'actual':actual,'selected_masses':p})
 F=min(z['actual'] for z in rows) if rows else None
 value=min(z for z in [U,C,F] if z is not None)
 return {'X_mask':X,'X':sorted(xs),'Y':sorted(ys),'x':x,'y':y,'q':q,'j':j,'uniform':U,
         'completion':C,'completion_domain':C is not None,'neighborhood_min':F,'certificate':value,
         'gap_above_target':value-R,'profiles':rows}
def encode(v):
 if isinstance(v,Q):return str(v)
 raise TypeError(type(v))
def serialized(v):return json.loads(json.dumps(v,default=encode))
def half_optimum(a,E,N):
 n=len(a);W=sum(a);limit=1<<n;m=[0]*limit;e=[0]*limit
 for s in range(1,limit):
  v=s.bit_length()-1;t=s^(1<<v);m[s]=m[t]+a[v]
  e[s]=e[t]+a[v]*sum(a[u] for u in N[v] if t>>u&1)
 best=None
 for v in range(n):
  for s in range(limit):
   if s>>v&1:continue
   rem=W-2*m[s]
   if 0<=rem<=2*a[v]:
    z=2*e[s]+rem*sum(a[u] for u in N[v] if s>>u&1)
    best=z if best is None else min(best,z)
 assert best is not None
 return Q(best,2*W*W)
def verify_case(z,E,N):
 a=z['integer_weights'];W=sum(a);n=len(a)
 minimum,ties,local=gray_cuts(a,E,N)
 assert z['minimum_internal_numerator']==minimum,'false maximum-cut optimum'
 assert Q(z['minimum_internal_cost'])==Q(minimum,W*W),'wrong edge normalization'
 assert z['global_tie_masks']==ties,'dropped or false tied global cut'
 assert z['global_ties_up_to_complement']==len(ties)
 assert z['cuts_up_to_complement']==1<<(n-1) and z['weight_sum']==W
 eligible=Q(minimum,W*W)<=I
 assert z['BCL_eligible']==eligible
 assert z['excluded_reason']==(None if eligible else 'minimum internal cost exceeds 2/47')
 cache={}
 def row(X):
  if X not in cache:cache[X]=certificate(a,E,N,X)
  return cache[X]
 orient=[X for s in ties for X in orientations(s,a)]
 expected=[{'X_mask':X,'certificate':str(row(X)['certificate'])} for X in orient]
 assert z['global_orientations']==expected,'dropped or false global orientation'
 values=[row(X)['certificate'] for X in orient];best=min(values);worst=max(values)
 assert Q(z['best_global_certificate'])==best and Q(z['worst_global_certificate'])==worst
 assert z['existential_failure']==(eligible and best>R),'existential quantifier wrong'
 assert z['worst_tie_failure']==(eligible and worst>R),'worst-tie quantifier wrong'
 for name,value in [('best_global_evidence',best),('worst_global_evidence',worst)]:
  X=min(X for X in orient if row(X)['certificate']==value)
  assert z[name]==serialized(row(X)),'incorrect detailed actual profile evidence'
 local_values=[row(X)['certificate'] for s,ok in local if ok for X in orientations(s,a)]
 assert z['local_cuts']==len(local) and z['eligible_local_cuts']==sum(ok for s,ok in local)
 assert z['eligible_local_orientations']==len(local_values)
 assert z['bad_local_orientations']==sum(v>R for v in local_values)
 assert z['best_local_certificate']==(str(min(local_values)) if local_values else None)
 assert z['worst_local_certificate']==(str(max(local_values)) if local_values else None)
 optimum=half_optimum(a,E,N);h=z['true_fractional_half']
 assert Q(h['cost'])==optimum,'false half optimum'
 p=list(map(Q,h['selected_masses']));w=[Q(v,W) for v in a]
 assert len(p)==n and sum(p)==Q(1,2) and all(0<=p[v]<=w[v] for v in range(n))
 assert cost(E,p)==optimum and sum(0<p[v]<w[v] for v in range(n))<=1
 s=h['full_mask'];partial=h['partial_vertex'];candidate=[w[v] if s>>v&1 else Q(0) for v in range(n)]
 if partial is not None:
  assert not(s>>partial&1);candidate[partial]=Q(h['partial_twice_mass'],2*W)
 assert candidate==p,'false optimum support'
 assert h['finite_blowup_order']==2*W and h['cluster_sizes']==[2*v for v in a]
 counts=h['selected_vertex_counts'];assert [Q(v,2*W) for v in counts]==p and sum(counts)==W
 global_rows=[row(X) for X in orient]
 diagnostic={'host':z['host'],'pattern':z['weight_pattern'],'best':str(best),'worst':str(worst),
   'optimum':str(optimum),'ties':len(ties),'orientations':len(orient),
   'old_bounds_both_fail':sum(min(t for t in [v['uniform'],v['completion']] if t is not None)>R for v in global_rows),
   'uniform_above_target':sum(v['uniform']>R for v in global_rows),
   'completion_above_target':sum(v['completion'] is not None and v['completion']>R for v in global_rows),
   'completion_unavailable':sum(v['completion'] is None for v in global_rows),
   'largest_old_certificate':str(max(min(t for t in [v['uniform'],v['completion']] if t is not None) for v in global_rows)),
   'largest_uniform_cost':str(max(v['uniform'] for v in global_rows))}
 return {'ties':len(ties),'orientations':len(orient),'eligible':eligible,'best':best,'worst':worst,
         'optimum':optimum,'local_bad':sum(v>R for v in local_values),'diagnostic':diagnostic}
def verify(d,config):
 assert Q(d['target'])==R and Q(d['internal_budget'])==I
 assert d['config_sha256']==hashlib.sha256((HERE/'INPUT-CONFIG.json').read_bytes()).hexdigest()
 assert [h['name'] for h in d['hosts']]==config['hosts']
 rng=random.Random(config['seed']);expected=[];graphs={}
 for h in d['hosts']:
  name=h['name'];n=h['n'];E=list(map(tuple,h['edges']));N=adjacency(n,E)
  assert E==expected_edges(name,n),'incorrect host definition';graphs[name]=(E,N)
  patterns=[('uniform',[1]*n),('root_neighborhood_double',[2 if v in N[0] else 1 for v in range(n)]),('alternating_1_2',[1+v%2 for v in range(n)])]
  patterns += [('seeded_'+str(i+1),[rng.randint(1,7) for _ in range(n)]) for i in range(3)]
  expected += [(name,k,a) for k,a in patterns]
 assert len(d['cases'])==len(expected)==42
 checks=[]
 for z,(name,kind,a) in zip(d['cases'],expected):
  assert (z['host'],z['weight_pattern'],z['integer_weights'])==(name,kind,a),'fixed sample changed'
  E,N=graphs[name];checks.append(verify_case(z,E,N))
 eligible=[x for x in checks if x['eligible']]
 expected_summary={'cases':42,'eligible_cases':len(eligible),'excluded_cases':42-len(eligible),
  'cuts_up_to_complement':sum(z['cuts_up_to_complement'] for z in d['cases']),
  'global_ties_up_to_complement':sum(z['ties'] for z in checks),'global_orientations':sum(z['orientations'] for z in checks),
  'existential_failures':sum(x['eligible'] and x['best']>R for x in checks),
  'worst_tie_failures':sum(x['eligible'] and x['worst']>R for x in checks),
  'bad_local_orientations':sum(x['local_bad'] for x in checks),
  'largest_best_global_certificate':max(x['best'] for x in eligible),
  'largest_worst_global_certificate':max(x['worst'] for x in eligible),
  'max_true_half_optimum':max(x['optimum'] for x in checks)}
 assert d['summary']==serialized(expected_summary),'summary mismatch'
 diagnostic=json.loads((HERE/'coverage-diagnostic.json').read_text());rows=[z['diagnostic'] for z in checks]
 assert diagnostic['cases']==rows,'diagnostic case mismatch'
 for field,source in [('total_old_unresolved_orientations','old_bounds_both_fail'),('total_uniform_above_target','uniform_above_target'),('total_completion_above_target','completion_above_target'),('total_completion_unavailable','completion_unavailable')]:
  assert diagnostic[field]==sum(r[source] for r in rows)
 for field in ['largest_old_certificate','largest_uniform_cost']:
  assert Q(diagnostic[field])==max(Q(r[field]) for r in rows)
 assert diagnostic['cases_with_best_worst_difference']==sum(r['best']!=r['worst'] for r in rows)
 return serialized(expected_summary)
def main():
 config=json.loads((HERE/'INPUT-CONFIG.json').read_text());d=json.loads((HERE/'screen-results.json').read_text())
 positive=verify(d,config);controls=[]
 for kind in ['wrong_cut_optimum','dropped_tied_cut','wrong_edge_normalization','triangle_host','wrong_half_optimum','dropped_equal_orientation']:
  bad=copy.deepcopy(d)
  if kind=='triangle_host':bad['hosts'][0]['edges'].append([1,2])
  elif kind=='dropped_tied_cut':next(z for z in bad['cases'] if len(z['global_tie_masks'])>1)['global_tie_masks'].pop()
  elif kind=='wrong_cut_optimum':bad['cases'][0]['minimum_internal_numerator']+=1
  elif kind=='wrong_edge_normalization':bad['cases'][0]['minimum_internal_cost']=str(2*Q(bad['cases'][0]['minimum_internal_cost']))
  elif kind=='wrong_half_optimum':next(z for z in bad['cases'] if Q(z['true_fractional_half']['cost'])>0)['true_fractional_half']['cost']='0'
  else:next(z for z in bad['cases'] if len(z['global_orientations'])>len(z['global_tie_masks']))['global_orientations'].pop()
  try:verify(bad,config)
  except (AssertionError,ValueError) as e:controls.append({'name':kind,'rejected':True,'reason':str(e)})
  else:raise AssertionError('negative accepted: '+kind)
 # A bad worst tie is not an existential failure. Check this exact truth table
 # even though the fixed sample has no bad worst tie.
 synthetic=[Q(3,125),Q(13,500)]
 assert min(synthetic)<R<max(synthetic)
 assert not(min(synthetic)>R) and max(synthetic)>R
 print(json.dumps({'passed':True,'independent_method':'Gray-code all-cut enumeration; independent partial-first half enumeration',
                   'summary':positive,'negative_controls':controls,
                   'existential_vs_worst_truth_table':{'values':list(map(str,synthetic)),'existential_failure':False,'worst_tie_failure':True}},indent=2))
if __name__=='__main__':main()

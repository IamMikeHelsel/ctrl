#!/usr/bin/env python3
"""Fixed E7 exact cut screen. Python standard library; no adaptive samples."""
from fractions import Fraction as F
from pathlib import Path
import json,random,time,hashlib,sys
HERE=Path(__file__).resolve().parent
R=F(1,40);I=F(2,47)
def encode(x):
 if isinstance(x,F):return str(x)
 raise TypeError(type(x))
def bits(s):
 while s:
  b=s&-s;yield b.bit_length()-1;s-=b
def graph(n,edges):
 edges=sorted(set(tuple(sorted(e)) for e in edges));adj=[0]*n
 for u,v in edges:
  assert 0<=u<v<n
  adj[u]|=1<<v;adj[v]|=1<<u
 for u,v in edges:assert not(adj[u]&adj[v]),'triangle'
 return edges,adj
def hosts():
 h={}
 h['Clebsch']=(16,[(u,v) for u in range(16) for v in range(u+1,16) if u^v in [1,2,4,8,15]])
 cyc=[(i,(i+1)%5) for i in range(5)]
 h['MycielskiC5']=(11,[*cyc,*[(u,v+5) for u,v in cyc],*[(v,u+5) for u,v in cyc],*[(i+5,10) for i in range(5)]])
 h['Petersen']=(10,[*cyc,*[(i,i+5) for i in range(5)],*[(i+5,5+(i+2)%5) for i in range(5)]])
 for k in range(3,7):
  n=3*k-1;h['Andrasfai'+str(k)]=(n,[(u,v) for u in range(n) for v in range(u+1,n) if k<=v-u<=2*k-1])
 return h
def arrays(a,adj):
 count=1<<len(a);m=[0]*count;e=[0]*count
 for s in range(1,count):
  b=s&-s;v=b.bit_length()-1;t=s-b
  m[s]=m[t]+a[v];e[s]=e[t]+a[v]*m[t&adj[v]]
 return m,e
def envelope(x):
 assert F(1,3)<=x<=F(1,2)
 return F(3,2)*x*x-F(5,4)*x+F(9,32) if x<=F(3,8) else x*(F(1,2)-x)/2
def orientations(s,m,W,full):
 if 2*m[s]<W:return [s]
 if 2*m[s]>W:return [full^s]
 return [s,full^s]
def cert(a,E,adj,m,e,X,details=False):
 n=len(a);W=sum(a);full=(1<<n)-1;Y=full^X;xm=m[X];ym=m[Y]
 assert 0<=xm<=ym and ym>0
 q=F(e[X],W*W);j=F(e[Y],W*W);u=F(e[Y],4*ym*ym)
 completion=envelope(F(xm,W))+q if 3*xm>=W else None
 fs=[];rows=[]
 if 2*ym>W:
  d={v:m[adj[v]&Y] for v in bits(Y)}
  for v in bits(Y):
   nv=adj[v]&Y;dv=d[v];sv=sum(a[z]*d[z] for z in bits(nv))
   if 2*dv<=2*ym-W:
    f=F(e[Y]-sv,4*(ym-dv)**2);branch='low'
    if details:p=[F(a[z],2*(ym-dv)) if Y>>z&1 and not(nv>>z&1) else F(0) for z in range(n)]
   else:
    f=F(2*dv*e[Y]-(2*ym-W)*sv,2*dv*W*W);branch='high'
    if details:p=[F(a[z],W)*(1-F(2*ym-W,2*dv)) if nv>>z&1 else (F(a[z],W) if Y>>z&1 else F(0)) for z in range(n)]
   fs.append(f)
   if details:
    assert sum(p)==F(1,2) and all(0<=p[z]<=F(a[z],W) for z in range(n))
    actual=sum(p[l]*p[r] for l,r in E);assert actual==f
    rows.append({'vertex':v,'d':F(dv,W),'s':F(sv,W*W),'branch':branch,'predicted':f,'actual':actual,'selected_masses':p})
 values=[u,*fs]
 if completion is not None:values.append(completion)
 result=min(values)
 if not details:return result
 return {'X_mask':X,'X':list(bits(X)),'Y':list(bits(Y)),'x':F(xm,W),'y':F(ym,W),
         'q':q,'j':j,'uniform':u,'completion':completion,'completion_domain':3*xm>=W,
         'neighborhood_min':min(fs) if fs else None,'certificate':result,
         'gap_above_target':result-R,'profiles':rows}
def half_optimum(a,E,adj,m,e):
 W=sum(a);n=len(a);best=None;winner=None;vertices=0
 for s in range(1<<n):
  rem=W-2*m[s]
  if rem<0:continue
  if rem==0:
   z=2*e[s];vertices+=1
   if best is None or z<best:best=z;winner=(s,None,0)
  else:
   for v in range(n):
    if not(s>>v&1) and rem<=2*a[v]:
     z=2*e[s]+rem*m[s&adj[v]];vertices+=1
     if best is None or z<best:best=z;winner=(s,v,rem)
 assert best is not None
 s,v,rem=winner;p=[F(a[z],W) if s>>z&1 else F(0) for z in range(n)]
 if v is not None:p[v]=F(rem,2*W)
 assert sum(p)==F(1,2) and all(0<=p[z]<=F(a[z],W) for z in range(n))
 assert sum(p[l]*p[r] for l,r in E)==F(best,2*W*W)
 assert sum(0<p[z]<F(a[z],W) for z in range(n))<=1
 return {'cost':F(best,2*W*W),'full_mask':s,'partial_vertex':v,'partial_twice_mass':rem,
         'selected_masses':p,'extreme_profiles_examined':vertices,
         'finite_blowup_order':2*W,'cluster_sizes':[2*z for z in a],
         'selected_vertex_counts':[int(z*2*W) for z in p]}
def case(name,kind,a,E,adj):
 n=len(a);W=sum(a);full=(1<<n)-1;m,e=arrays(a,adj)
 minimum=min(e[s]+e[full^s] for s in range(0,1<<n,2))
 ties=[s for s in range(0,1<<n,2) if e[s]+e[full^s]==minimum]
 eligible=47*minimum<=2*W*W;cache={};oriented=[]
 def value(X):
  if X not in cache:cache[X]=cert(a,E,adj,m,e,X)
  return cache[X]
 for s in ties:
  for X in orientations(s,m,W,full):oriented.append((X,value(X)))
 best=min(z[1] for z in oriented);worst=max(z[1] for z in oriented)
 bestX=min(X for X,z in oriented if z==best);worstX=min(X for X,z in oriented if z==worst)
 local=eligible_local=local_oriented=bad_local=0;local_best=None;local_worst=None
 for s in range(0,1<<n,2):
  if not all(2*m[adj[v]&(s if s>>v&1 else full^s)]<=m[adj[v]] for v in range(n)):continue
  local+=1
  if 47*(e[s]+e[full^s])>2*W*W:continue
  eligible_local+=1
  for X in orientations(s,m,W,full):
   z=value(X);local_oriented+=1;bad_local+=z>R
   local_best=z if local_best is None else min(local_best,z)
   local_worst=z if local_worst is None else max(local_worst,z)
 half=half_optimum(a,E,adj,m,e)
 return {'host':name,'weight_pattern':kind,'integer_weights':a,'weight_sum':W,
         'cuts_up_to_complement':1<<(n-1),'minimum_internal_numerator':minimum,
         'minimum_internal_cost':F(minimum,W*W),'BCL_eligible':eligible,
         'excluded_reason':None if eligible else 'minimum internal cost exceeds 2/47',
         'global_tie_masks':ties,'global_ties_up_to_complement':len(ties),
         'global_orientations':[{'X_mask':X,'certificate':z} for X,z in oriented],
         'best_global_certificate':best,'worst_global_certificate':worst,
         'existential_failure':eligible and best>R,'worst_tie_failure':eligible and worst>R,
         'best_global_evidence':cert(a,E,adj,m,e,bestX,True),
         'worst_global_evidence':cert(a,E,adj,m,e,worstX,True),
         'local_cuts':local,'eligible_local_cuts':eligible_local,'eligible_local_orientations':local_oriented,
         'bad_local_orientations':bad_local,'best_local_certificate':local_best,'worst_local_certificate':local_worst,
         'true_fractional_half':half}
def main():
 start=time.monotonic();config=json.loads((HERE/'INPUT-CONFIG.json').read_text())
 assert config['seed']==2026101807 and config['total_cases']==42
 rng=random.Random(config['seed']);hs=hosts();records=[];cases=[]
 for name in config['hosts']:
  n,raw=hs[name];E,adj=graph(n,raw);records.append({'name':name,'n':n,'edges':E})
  patterns=[('uniform',[1]*n),('root_neighborhood_double',[2 if adj[0]>>v&1 else 1 for v in range(n)]),('alternating_1_2',[1+v%2 for v in range(n)])]
  patterns += [('seeded_'+str(i+1),[rng.randint(config['random_weight_min'],config['random_weight_max']) for _ in range(n)]) for i in range(config['random_vectors_per_host'])]
  for kind,a in patterns:
   cases.append(case(name,kind,a,E,adj))
   assert time.monotonic()-start<config['max_seconds'],'fixed CPU screen exceeded time cap'
 assert len(cases)==config['total_cases']
 eligible=[z for z in cases if z['BCL_eligible']]
 summary={'cases':len(cases),'eligible_cases':len(eligible),'excluded_cases':len(cases)-len(eligible),
          'cuts_up_to_complement':sum(z['cuts_up_to_complement'] for z in cases),
          'global_ties_up_to_complement':sum(z['global_ties_up_to_complement'] for z in cases),
          'global_orientations':sum(len(z['global_orientations']) for z in cases),
          'existential_failures':sum(z['existential_failure'] for z in cases),
          'worst_tie_failures':sum(z['worst_tie_failure'] for z in cases),
          'bad_local_orientations':sum(z['bad_local_orientations'] for z in cases),
          'largest_best_global_certificate':max(z['best_global_certificate'] for z in eligible),
          'largest_worst_global_certificate':max(z['worst_global_certificate'] for z in eligible),
          'max_true_half_optimum':max(z['true_fractional_half']['cost'] for z in cases)}
 out={'config_sha256':hashlib.sha256((HERE/'INPUT-CONFIG.json').read_bytes()).hexdigest(),
      'target':R,'internal_budget':I,'hosts':records,'cases':cases,'summary':summary,
      'seconds':time.monotonic()-start,'python':sys.version,'scope':'Fixed finite screen; no universal theorem'}
 print(json.dumps(out,default=encode,indent=2))
if __name__=='__main__':main()

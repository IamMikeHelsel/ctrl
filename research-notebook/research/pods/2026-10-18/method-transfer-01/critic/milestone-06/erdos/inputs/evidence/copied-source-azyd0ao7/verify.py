#!/usr/bin/env python3
"""Independent read-only verification; does not import experiment.py."""
from fractions import Fraction as Q
from pathlib import Path
import json,copy,random
HERE=Path(__file__).resolve().parent;I=Q(2,47);R=Q(1,40)
def mass(profile):return sum(profile,Q(0))
def cost(E,p):return sum((p[u]*p[v] for u,v in E),Q(0))
def graph(n,E):
 assert len(E)==len(set(E)) and all(0<=u<v<n for u,v in E),'invalid simple graph'
 N=[set() for _ in range(n)]
 for u,v in E:N[u].add(v);N[v].add(u)
 for u,v in E:assert not N[u]&N[v],'triangle violates hypothesis'
 return N

def envelope(x):
 assert Q(1,3)<=x<=Q(1,2),'completion outside formal domain'
 return 3*x*x/2-5*x/4+Q(9,32) if x<=Q(3,8) else x*(Q(1,2)-x)/2

def certificate(w,E,N,X):
 Y=set(range(len(w)))-X;x=mass(w[v] for v in X);y=1-x;assert x<=y and y>0
 q=cost([(u,v) for u,v in E if u in X and v in X],w)
 j=cost([(u,v) for u,v in E if u in Y and v in Y],w)
 U=j/(4*y*y);B=envelope(x)+q if x>=Q(1,3) else None
 values=[];rows=[]
 if y>Q(1,2):
  b=y-Q(1,2)
  deg={v:mass(w[u] for u in N[v]&Y) for v in Y}
  for v in sorted(Y):
   neigh=N[v]&Y;d=deg[v];s=mass(w[u]*deg[u] for u in neigh)
   if d<=b:
    p=[w[u]/(2*(y-d)) if u in Y-neigh else Q(0) for u in range(len(w))];formula=(j-s)/(4*(y-d)**2);branch='low'
   else:
    p=[w[u]*(1-b/d) if u in neigh else (w[u] if u in Y else Q(0)) for u in range(len(w))];formula=j-b*s/d;branch='high'
   assert mass(p)==Q(1,2) and all(0<=p[u]<=w[u] for u in range(len(w)))
   actual=cost(E,p);assert actual==formula
   values.append(actual);rows.append((v,d,s,branch,p,actual))
 choices=[U,*values]
 if B is not None:choices.append(B)
 return {'x':x,'y':y,'c':1/(2*y),'q':q,'j':j,'cut_cost':q+j,'uniform_cost':U,
         'completion_bound':B,'completion_domain':x>=Q(1,3),'certificate':min(choices),
         'certificate_gap':min(choices)-R},rows

def check_cut(w,E,N,record,need_local=True):
 n=len(w);X=set(record['X']);assert len(X)==len(record['X'])
 Y=set(record['Y']);assert X.isdisjoint(Y) and X|Y==set(range(n))
 data,rows=certificate(w,E,N,X)
 checks=[]
 for v in range(n):
  side=X if v in X else Y;inside=mass(w[u] for u in N[v]&side);outside=mass(w[u] for u in N[v]-side)
  if need_local:assert inside<=outside,'cut is not single-vertex locally optimal'
  checks.append((inside,outside,outside-inside))
 for key,value in data.items():
  got=record[key]
  if value is None:assert got is None
  elif isinstance(value,bool):assert got==value
  else:assert Q(got)==value,'incorrect recorded '+key
 assert len(record['local_degree_checks'])==n
 for v,(inside,outside,margin) in enumerate(checks):
  z=record['local_degree_checks'][v];assert z['vertex']==v
  assert (Q(z['internal_degree']),Q(z['external_degree']),Q(z['margin']))==(inside,outside,margin)
 assert record['single_vertex_local']==all(z[2]>=0 for z in checks)
 assert len(rows)==len(record['neighborhood_profiles'])
 for row,z in zip(rows,record['neighborhood_profiles']):
  v,d,s,branch,p,actual=row
  assert (z['vertex'],Q(z['d']),Q(z['s']),z['branch'])==(v,d,s,branch)
  assert Q(z['actual'])==Q(z['predicted'])==actual,'false profile cost'
  if 'selected_masses' in z:assert list(map(Q,z['selected_masses']))==p
 return data,checks

def verify_counter(d):
 c=d['counterexample'];n=c['n'];assert n==28
 w=list(map(Q,c['weights']));E=list(map(tuple,c['edges']))
 assert len(w)==n and all(a>0 for a in w) and mass(w)==1
 N=graph(n,E)
 bad,checks=check_cut(w,E,N,c['bad_local_cut']);good,_=check_cut(w,E,N,c['global_maximum_cut'])
 assert bad['x']==Q(401,1000) and bad['y']==Q(599,1000)
 assert bad['cut_cost']==I and bad['certificate']-R==Q(199,9600000)>0
 assert min(z[2] for z in checks)==Q(1817,24000)>0
 assert bad['uniform_cost']==Q(5,192) and bad['completion_bound']-R==Q(62237,2256000000)>0
 assert len(E)==109
 assert good['cut_cost']==0 and good['certificate']==0,'claimed global zero-cut certificate has positive internal cost'
 A,B=map(set,c['global_colors']);assert A.isdisjoint(B) and A|B==set(range(n))
 assert all((u in A)!=(v in A) for u,v in E)
 assert mass(w[v] for v in A)==mass(w[v] for v in B)==Q(1,2)
 p=list(map(Q,c['true_fractional_half']['selected_masses']))
 assert mass(p)==Q(1,2),'wrong half mass'
 assert all(0<=p[v]<=w[v] for v in range(n)) and cost(E,p)==0
 assert Q(c['true_fractional_half']['cost'])==0
 # Every edge cost is nonnegative for every feasible profile. The zero witness
 # therefore certifies the global optimum without enumerating 2^28 supports.
 Y=set(c['bad_local_cut']['Y']);y=bad['y'];b=y-Q(1,2)
 degrees=[mass(w[u] for u in N[v]&Y) for v in sorted(Y)]
 assert all(z==5*y/24 for z in degrees)
 yp=list(map(Q,c['true_Y_restricted_half']['selected_masses']))
 assert mass(yp)==Q(1,2) and all(0<=yp[v]<=w[v] for v in range(n))
 assert all(yp[v]==0 for v in set(range(n))-Y)
 deleted=[w[v]-yp[v] if v in Y else Q(0) for v in range(n)]
 assert mass(deleted)==b and cost(E,deleted)==0
 lower=bad['j']-(5*y/24)*b
 assert cost(E,yp)==lower==Q(c['true_Y_restricted_half']['cost'])==bad['certificate']
 assert sum(0<yp[v]<w[v] for v in range(n))<=1
 # Expansion gives any Y-supported half cost = lower + cost(deleted)>=lower.
 blow=c['finite_simple_blowup'];W=blow['order'];a=blow['cluster_sizes']
 assert W==22560000 and W%2==0 and sum(a)==W and all(z>0 for z in a)
 assert [Q(z,W) for z in a]==w and blow['half_size']==W//2
 assert sum(a[v] for v in A)==W//2
 assert all((w[v]*W).denominator==1 for v in range(n))
 return {'vertices':n,'edges':len(E),'implicit_blowup_order':W,
         'local_certificate':str(bad['certificate']),'gap_above_025':str(bad['certificate_gap']),
         'strict_local_degree_margin':str(min(z[2] for z in checks)),
         'global_max_cut_certificate':'0','true_global_half_optimum':'0','true_Y_restricted_half_optimum':str(lower)}

def independently_enumerate(a,E):
 n=len(a);W=sum(a);full=(1<<n)-1;N=graph(n,E)
 subsets=range(1<<n)
 masses=[sum(a[v] for v in range(n) if s>>v&1) for s in subsets]
 inside=[sum(a[u]*a[v] for u,v in E if s>>u&1 and s>>v&1) for s in subsets]
 cuts=[]
 for s in range(0,1<<n,2):
  inn=inside[s]+inside[full^s]
  local=all(sum(a[u] for u in N[v] if bool(s>>u&1)==bool(s>>v&1))<=
            sum(a[u] for u in N[v] if bool(s>>u&1)!=bool(s>>v&1)) for v in range(n))
  cuts.append((s,inn,local))
 minimum=min(z[1] for z in cuts);counts={'local_cuts':0,'BCL_eligible_local_cuts':0,'bad_eligible_local_certificates':0,
  'global_maximum_cuts':0,'bad_BCL_eligible_global_certificates':0}
 worstL=worstG=Q(0);w=[Q(z,W) for z in a]
 for s,inn,local in cuts:
  counts['local_cuts']+=local
  eligible=Q(inn,W*W)<=I;glob=inn==minimum
  if not glob and not(local and eligible):continue
  X={v for v in range(n) if s>>v&1}
  if 2*masses[s]>W:X=set(range(n))-X
  cert,_=certificate(w,E,N,X);value=cert['certificate']
  if glob:
   counts['global_maximum_cuts']+=1;worstG=max(worstG,value)
   if eligible:counts['bad_BCL_eligible_global_certificates']+=value>R
  if local and eligible:
   counts['BCL_eligible_local_cuts']+=1;worstL=max(worstL,value);counts['bad_eligible_local_certificates']+=value>R
 # Independent extreme-point enumeration: choose partial vertex first, then
 # all full subsets of its complement. Endpoint duplicates do not affect min.
 best=None
 for v in range(n):
  for s in subsets:
   if s>>v&1:continue
   rem=W-2*masses[s]
   if not 0<=rem<=2*a[v]:continue
   value=2*inside[s]+rem*sum(a[u] for u in N[v] if s>>u&1)
   best=value if best is None else min(best,value)
 assert best is not None
 return counts,worstL,worstG,Q(minimum,W*W),Q(best,2*W*W)

def verify(d):
 assert Q(d['target'])==R and Q(d['BCL'])==I
 counter=verify_counter(d);hosts={h['name']:h for h in d['hosts']};assert set(hosts)=={'K2','C4','C5','C7','Petersen','Andrasfai3','Andrasfai4','Andrasfai5'}
 rng=random.Random(2026101806);assert d['seed']==2026101806
 expected=[]
 for name,h in hosts.items():
  n=h['n'];E=list(map(tuple,h['edges']));graph(n,E)
  if name.startswith('Andrasfai'):
   k=int(name[-1]);assert n==3*k-1
   for u in range(n):
    for v in range(u+1,n):
     assert ((u,v) in E)==(abs((3*u)%n-(3*v)%n)%3==1)
  expected += [(name,[1]*n),*[(name,[rng.randint(1,7) for _ in range(n)]) for _ in range(2)]]
 assert len(d['sanities'])==len(expected)==24
 total_cuts=0;total_eligible=0
 for z,(name,a) in zip(d['sanities'],expected):
  h=hosts[name];E=list(map(tuple,h['edges']));assert z['host']==name and z['integer_weights']==a and z['n']==h['n']
  counts,L,G,minimum,opt=independently_enumerate(a,E)
  assert z['cuts_examined_up_to_complement']==1<<(h['n']-1)
  total_cuts+=z['cuts_examined_up_to_complement'];total_eligible+=counts['BCL_eligible_local_cuts']
  for k,v in counts.items():assert z[k]==v
  assert Q(z['worst_local_certificate'])==L and Q(z['worst_global_certificate'])==G
  assert Q(z['global_internal_cost'])==minimum
  assert Q(z['true_fractional_half']['cost'])==opt,'false fractional-half optimum'
  witness=z['true_fractional_half']['witness'];W=sum(a)
  p=[Q(a[v],W) if witness['full_mask']>>v&1 else Q(0) for v in range(len(a))]
  v=witness['partial_vertex']
  if v is not None:
   assert 0<=v<len(a) and not (witness['full_mask']>>v&1)
   p[v]=Q(witness['partial_twice_mass'],2*W)
  assert mass(p)==Q(1,2) and all(0<=p[v]<=Q(a[v],W) for v in range(len(a))),'invalid optimum witness'
  assert cost(E,p)==opt,'false optimum witness cost'
  assert sum(0<p[v]<Q(a[v],W) for v in range(len(a)))<=1
  if name=='C5' and len(set(a))==1:assert opt==Q(1,50)
  if name in ['K2','C4']:assert opt==0
 return {'counterexample':counter,'sanity_cases':24,'enumerated_cuts_up_to_complement':total_cuts,
         'eligible_local_sanity_cuts':total_eligible,'all_sanity_optima_recomputed':True,
         'andrasfai_standard_definition_isomorphism_checked':True}

def main():
 d=json.loads((HERE/'results-development.json').read_text());positive=verify(d);mutants=[]
 for name in ['remove_cross_edges','add_triangle','false_neighborhood_cost','wrong_half_mass','false_global_cut','false_C5_optimum']:
  bad=copy.deepcopy(d);c=bad['counterexample']
  if name=='remove_cross_edges':c['edges']=[e for e in c['edges'] if (e[0]<4)==(e[1]<4)]
  elif name=='add_triangle':c['edges']=sorted(c['edges']+[[4,5]])
  elif name=='false_neighborhood_cost':c['bad_local_cut']['neighborhood_profiles'][0]['actual']='0'
  elif name=='wrong_half_mass':c['true_fractional_half']['selected_masses'][0]='0'
  elif name=='false_global_cut':c['global_maximum_cut']=copy.deepcopy(c['bad_local_cut'])
  else:next(z for z in bad['sanities'] if z['host']=='C5')['true_fractional_half']['cost']='0'
  try:verify(bad)
  except (AssertionError,ValueError) as e:mutants.append({'name':name,'rejected':True,'reason':str(e)})
  else:raise AssertionError('negative accepted: '+name)
 print(json.dumps({'passed':True,'positive':positive,'negative_controls':mutants},indent=2))
if __name__=='__main__':main()

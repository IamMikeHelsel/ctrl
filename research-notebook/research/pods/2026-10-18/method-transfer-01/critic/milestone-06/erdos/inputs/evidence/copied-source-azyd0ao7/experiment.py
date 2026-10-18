#!/usr/bin/env python3
"""Exact local-cut falsifier and bounded finite sanity checks. Standard library."""
from fractions import Fraction as F
from pathlib import Path
import json,random,itertools,time,math
I=F(2,47);R=F(1,40);SEED=2026101806
HERE=Path(__file__).resolve().parent

def edge_set(pairs):return sorted({tuple(sorted(e)) for e in pairs})
def adjacency(n,edges):
 adj=[0]*n
 for u,v in edges:
  assert 0<=u<v<n
  adj[u]|=1<<v;adj[v]|=1<<u
 for u,v in edges:assert not(adj[u]&adj[v]),'triangle'
 return adj

def mask_items(mask):
 while mask:
  bit=mask&-mask;yield bit.bit_length()-1;mask-=bit

def profile_cost(w,edges,p):return sum(p[u]*p[v] for u,v in edges)
def Q(x):
 assert F(1,3)<=x<=F(1,2)
 return F(3,2)*x*x-F(5,4)*x+F(9,32) if x<=F(3,8) else x*(F(1,2)-x)/2

def cut_evidence(w,edges,maskX,profiles=True):
 n=len(w);adj=adjacency(n,edges);full=(1<<n)-1;X=set(mask_items(maskX));Y=set(range(n))-X
 x=sum(w[v] for v in X);y=sum(w[v] for v in Y)
 assert sum(w)==1 and all(z>0 for z in w) and x<=y and y>0
 q=sum(w[u]*w[v] for u,v in edges if u in X and v in X)
 j=sum(w[u]*w[v] for u,v in edges if u in Y and v in Y)
 local=[]
 for v in range(n):
  same=X if v in X else Y;inn=sum(w[u] for u in mask_items(adj[v]) if u in same)
  out=sum(w[u] for u in mask_items(adj[v]) if u not in same)
  local.append({'vertex':v,'internal_degree':inn,'external_degree':out,'margin':out-inn})
 c=1/(2*y);p=[c*w[v] if v in Y else F(0) for v in range(n)]
 assert sum(p)==F(1,2) and all(0<=p[v]<=w[v] for v in range(n))
 uniform=profile_cost(w,edges,p);assert uniform==c*c*j
 completion=Q(x)+q if x>=F(1,3) else None
 rows=[]
 if y>F(1,2):
  b=y-F(1,2);deg={v:sum(w[u] for u in mask_items(adj[v]) if u in Y) for v in Y}
  for v in sorted(Y):
   neigh=set(mask_items(adj[v]))&Y;d=deg[v];s=sum(w[u]*deg[u] for u in neigh)
   if d<=b:
    p=[w[u]/(2*(y-d)) if u in Y-neigh else F(0) for u in range(n)]
    predicted=(j-s)/(4*(y-d)**2);branch='low'
   else:
    p=[w[u]*(1-b/d) if u in neigh else (w[u] if u in Y else F(0)) for u in range(n)]
    predicted=j-b*s/d;branch='high'
   actual=profile_cost(w,edges,p)
   assert all(0<=p[u]<=w[u] for u in range(n)) and sum(p)==F(1,2)
   assert predicted==actual
   row={'vertex':v,'d':d,'s':s,'branch':branch,'predicted':predicted,'actual':actual}
   if profiles:row['selected_masses']=p
   rows.append(row)
 candidates=[uniform,*[z['actual'] for z in rows]]
 if completion is not None:candidates.append(completion)
 return {'X':sorted(X),'Y':sorted(Y),'x':x,'y':y,'c':c,'q':q,'j':j,'cut_cost':q+j,
         'local_degree_checks':local,'single_vertex_local':all(z['margin']>=0 for z in local),
         'uniform_cost':uniform,'completion_bound':completion,'completion_domain':x>=F(1,3),
         'neighborhood_profiles':rows,'certificate':min(candidates),
         'certificate_gap':min(candidates)-R}

def counterexample():
 y=F(599,1000);x=1-y;j=F(5,48)*y*y;q=I-j
 # Global color classes: X vertices0,2 and Y left4..15; X1,3 and Y right16..27.
 w=[F(1,20),20*q,x/2-F(1,20),x/2-20*q]+[y/24]*24
 assert all(a>0 for a in w) and sum(w)==1
 left=set([0,2,*range(4,16)]);right=set(range(28))-left
 edges=[(0,1)]
 edges += [(4+i,16+(i+t)%12) for i in range(12) for t in range(5)]
 edges += [(u,v) for u in [0,2] for v in range(16,28)]
 edges += [(u,v) for u in [1,3] for v in range(4,16)]
 edges=edge_set(edges);adjacency(28,edges)
 assert all((u in left)!=(v in left) for u,v in edges)
 local=cut_evidence(w,edges,15)
 assert local['single_vertex_local'] and all(z['margin']>0 for z in local['local_degree_checks'])
 assert local['cut_cost']==I and local['q']==q and local['j']==j
 assert local['certificate']>R
 assert local['uniform_cost']==F(5,192)
 assert all(z['actual']==F(5,48)*y*(1-y)>R for z in local['neighborhood_profiles'])
 mask=sum(1<<v for v in left);global_cut=cut_evidence(w,edges,mask)
 assert global_cut['x']==F(1,2) and global_cut['y']==F(1,2) and global_cut['cut_cost']==0
 assert global_cut['certificate']==0 and global_cut['single_vertex_local']
 half=[w[v] if v in left else F(0) for v in range(28)]
 assert sum(half)==F(1,2) and profile_cost(w,edges,half)==0
 # The true optimum restricted to Y follows from regular degrees and an
 # independent deletion support. Give an extreme-point witness explicitly.
 yhalf=[F(0)]*4+w[4:];remaining=y-F(1,2)
 for v in range(4,16):
  delete=min(remaining,w[v]);yhalf[v]-=delete;remaining-=delete
 assert remaining==0 and sum(yhalf)==F(1,2)
 assert sum(0<yhalf[v]<w[v] for v in range(28))<=1
 restricted_cost=profile_cost(w,edges,yhalf)
 assert restricted_cost==F(5,48)*y*(1-y)==local['certificate']
 N=math.lcm(*(z.denominator for z in w));N=N if N%2==0 else 2*N
 counts=[int(N*z) for z in w];assert all(F(k,N)==z for k,z in zip(counts,w))
 assert sum(counts)==N and N%2==0
 # A globally maximal cut is certified by internal cost0 and nonnegative edges.
 return {'n':28,'weights':w,'edges':edges,'global_colors':[sorted(left),sorted(right)],
         'bad_local_cut':local,'global_maximum_cut':global_cut,
         'true_fractional_half':{'selected_masses':half,'cost':F(0),'optimality':'all edge contributions are nonnegative'},
         'true_Y_restricted_half':{'selected_masses':yhalf,'cost':restricted_cost,'optimality':'regular Y gives j-mu*b plus nonnegative deleted-edge mass; this witness deletes only in an independent color'},
         'finite_simple_blowup':{'order':N,'cluster_sizes':counts,'half_size':N//2,'implicit_only':True},
         'global_cut_optimality':'internal cut cost0 is minimal since edge weights are nonnegative',
         'scope':'Refutes the retained envelope/profile certificate at a locally optimal cut; not every possible completion output.'}

def hosts():
 out={'K2':(2,[(0,1)])}
 for n in [4,5,7]:out['C'+str(n)]=(n,edge_set((i,(i+1)%n) for i in range(n)))
 out['Petersen']=(10,edge_set([*( (i,(i+1)%5) for i in range(5)),*((i,i+5) for i in range(5)),*((i+5,5+(i+2)%5) for i in range(5))]))
 for k in [3,4,5]:
  n=3*k-1;out['Andrasfai'+str(k)]=(n,[(u,v) for u in range(n) for v in range(u+1,n) if (v-u)%n in range(k,2*k)])
 return out

def arrays(a,edges):
 n=len(a);adj=adjacency(n,edges);size=1<<n;mass=[0]*size;cost=[0]*size
 for s in range(1,size):
  bit=s&-s;v=bit.bit_length()-1;t=s-bit;mass[s]=mass[t]+a[v]
  cost[s]=cost[t]+a[v]*mass[t&adj[v]]
 return adj,mass,cost

def optimum_half(a,adj,mass,cost):
 W=sum(a);best=None;witness=None;vertices_examined=0
 for s in range(1<<len(a)):
  rem=W-2*mass[s]
  if rem<0:continue
  if rem==0:
   val=2*cost[s];vertices_examined+=1
   if best is None or val<best:best=val;witness={'full_mask':s,'partial_vertex':None,'partial_twice_mass':0}
  else:
   for v in range(len(a)):
    if not(s>>v&1) and rem<=2*a[v]:
     val=2*cost[s]+rem*mass[s&adj[v]];vertices_examined+=1
     if best is None or val<best:best=val;witness={'full_mask':s,'partial_vertex':v,'partial_twice_mass':rem}
 assert best is not None
 return {'cost':F(best,2*W*W),'witness':witness,'box_slice_vertices_examined':vertices_examined}

def sanity_case(name,n,edges,a):
 W=sum(a);full=(1<<n)-1;adj,mass,cost=arrays(a,edges);w=[F(z,W) for z in a]
 minimum=min(cost[s]+cost[full^s] for s in range(0,1<<n,2))
 all_local=eligible_local=bad_local=0;global_count=bad_global=0;worst_local=F(0);worst_global=F(0)
 for s in range(0,1<<n,2):
  internal=cost[s]+cost[full^s]
  local=all(2*mass[adj[v]&(s if s>>v&1 else full^s)]<=mass[adj[v]] for v in range(n))
  all_local+=local
  glob=internal==minimum
  if not glob and not(local and F(internal,W*W)<=I):continue
  X=s if 2*mass[s]<=W else full^s
  evidence=cut_evidence(w,edges,X,False);assert evidence['single_vertex_local']==local
  if glob:
   global_count+=1;worst_global=max(worst_global,evidence['certificate'])
   if F(internal,W*W)<=I:bad_global+=evidence['certificate']>R
  if local and F(internal,W*W)<=I:
   eligible_local+=1;worst_local=max(worst_local,evidence['certificate']);bad_local+=evidence['certificate']>R
 half=optimum_half(a,adj,mass,cost)
 # Validate the actual extreme-point witness without the enumeration formula.
 ww=half['witness'];selected=[w[v] if ww['full_mask']>>v&1 else F(0) for v in range(n)]
 if ww['partial_vertex'] is not None:selected[ww['partial_vertex']]=F(ww['partial_twice_mass'],2*W)
 assert sum(selected)==F(1,2) and all(0<=selected[v]<=w[v] for v in range(n))
 assert profile_cost(w,edges,selected)==half['cost']
 return {'host':name,'n':n,'integer_weights':a,'cuts_examined_up_to_complement':1<<(n-1),
         'local_cuts':all_local,'BCL_eligible_local_cuts':eligible_local,'bad_eligible_local_certificates':bad_local,
         'global_maximum_cuts':global_count,'global_internal_cost':F(minimum,W*W),
         'bad_BCL_eligible_global_certificates':bad_global,'worst_local_certificate':worst_local,
         'worst_global_certificate':worst_global,'true_fractional_half':half}

def encode(v):
 if isinstance(v,F):return str(v)
 raise TypeError(type(v))
def main():
 started=time.monotonic();counter=counterexample();rng=random.Random(SEED);sanities=[];host_records=[]
 for name,(n,edges) in hosts().items():
  adjacency(n,edges);host_records.append({'name':name,'n':n,'edges':edges})
  for a in [[1]*n,*[[rng.randint(1,7) for _ in range(n)] for _ in range(2)]]:
   sanities.append(sanity_case(name,n,edges,a))
 out={'kind':'Exact structural falsifier plus bounded finite sanity checks; no universal positive claim',
      'target':R,'BCL':I,'seed':SEED,'counterexample':counter,'hosts':host_records,'sanities':sanities,
      'seconds':time.monotonic()-started,'broad_search_stopped':True,'remote_job_required':False}
 print(json.dumps(out,indent=2,default=encode))
if __name__=='__main__':main()

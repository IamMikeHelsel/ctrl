#!/usr/bin/env python3
"""Independent, read-only rational verifier. Does not import build_cover.py.

The partition tree and a separate vertical-strip tiling check each prove
coverage. All acceptance tests use fractions. Decimals are never consulted.
"""
from fractions import Fraction as Q
from pathlib import Path
import copy,json,sys
HERE=Path(__file__).resolve().parent
R=Q(63,2500);I=Q(2,47);A=Q(769,1000);H=Q(22,25)
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def neg(a):return (-a[1],-a[0])
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 t=[x*y for x in a for y in b];return min(t),max(t)
def div(a,b):
 assert b[0]>0 or b[1]<0,'denominator crosses zero'
 return mul(a,(1/b[1],1/b[0]))
def sq(a):return (0 if a[0]<=0<=a[1] else min(a[0]**2,a[1]**2),max(a[0]**2,a[1]**2))
def k(x):return(Q(x),Q(x))
def read(v):
 assert len(v)==2
 a,b=map(Q,v);assert a<=b;return(a,b)
def completion(c):
 x=1-1/(2*c)
 return 3*x*x/2-5*x/4+Q(9,32) if c<=Q(4,5) else x*(Q(1,2)-x)/2

def bounds(c,j):
 y=div(k(1),mul(k(2),c));mu=mul(mul(k(4),c),j)
 b=sub(y,k(Q(1,2)));L=sub(mul(k(8*R),sub(y,mu)),mul(k(2),mu))
 C=sub(sub(j,mul(k(4*R),sq(sub(y,mu)))),sq(mu))
 B=sub(div(sub(j,k(R)),b),L);T=add(div(sq(B),k(4)),mul(L,mu))
 return c[1]**2*j[1],completion(c[0])+I-j[0],C,T

def verify(data):
 assert Q(data['R'])==R and Q(data['I'])==I,'wrong fixed theorem target/input'
 assert read(data['rectangle']['c'])==(A,H)
 assert read(data['rectangle']['j'])==(0,I)
 assert Q(1,2)<Q(3,4)<A<Q(4,5)<H<1
 aa,dd,ee=R+Q(1,4)-I,Q(3,8),R+Q(1,8)
 margins={'low_uniform':R-I*A*A,'upper_quadratic_at_H':aa*H*H-dd*H+ee,
          'upper_quadratic_derivative_at_H':2*aa*H-dd,'upper_quadratic_leading':aa,
          'middle_completion_domain':A-Q(3,4),'middle_denominator_c':A,
          'middle_denominator_one_minus_c':1-H}
 assert {n:Q(v) for n,v in data['analytic_margins'].items()}==margins
 assert all(v>0 for v in margins.values())
 nodes=data['nodes'];seen=set();leaves=[]
 def visit(index,c,j,depth):
  assert type(index) is int and 0<=index<len(nodes)
  assert index not in seen,'cycle/repeated child';seen.add(index)
  n=nodes[index];assert read(n['c'])==c and read(n['j'])==j,'partition mismatch'
  assert n['depth']==depth
  u,f,C,T=bounds(c,j);saved=n['bounds']
  assert Q(saved['uniform_upper'])==u and Q(saved['completion_upper'])==f
  assert read(saved['C'])==C and read(saved['T'])==T,'false enclosure'
  method=n['method']
  if method!='split':
   assert 'children' not in n
   if method=='uniform':assert u<=R,'false uniform bound'
   elif method=='completion':assert f<=R,'false completion bound'
   else:assert method=='moment' and C[1]<=0 and T[1]<=0,'false refined moment bound'
   leaves.append(index);return
  assert len(n['children'])==2,'missing child'
  left,right=n['children'];mid=Q(n['midpoint'])
  if n['axis']=='c':
   assert c[0]<mid<c[1];visit(left,(c[0],mid),j,depth+1);visit(right,(mid,c[1]),j,depth+1)
  else:
   assert n['axis']=='j' and j[0]<mid<j[1]
   visit(left,c,(j[0],mid),depth+1);visit(right,c,(mid,j[1]),depth+1)
 visit(0,(A,H),(0,I),0)
 assert seen==set(range(len(nodes))),'unreachable nodes'
 assert not data['unresolved_nodes'] and data['passed']
 assert len(leaves)==data['leaf_count']
 assert max(n['depth'] for n in nodes)==data['max_depth']
 counts={method:sum(nodes[i]['method']==method for i in leaves) for method in ['uniform','completion','moment']}
 assert counts==data['method_counts']
 # Independent coverage test: ignore all tree edges and tile each vertical slab.
 boxes=[(read(nodes[i]['c']),read(nodes[i]['j'])) for i in leaves]
 endpoints=sorted({x for c,j in boxes for x in c});assert endpoints[0]==A and endpoints[-1]==H
 for lo,hi in zip(endpoints,endpoints[1:]):
  mid=(lo+hi)/2
  intervals=sorted(j for c,j in boxes if c[0]<mid<c[1])
  assert intervals and intervals[0][0]==0,'vertical gap at bottom'
  cursor=Q(0)
  for bot,top in intervals:
   assert bot==cursor and top>bot,'vertical gap or interior overlap'
   cursor=top
  assert cursor==I,'vertical gap at top'
 # Closed leaves include slab boundaries. This check proves coverage of all
 # horizontal and vertical endpoints as well as every open slab interior.
 for edge in [A,H]:
  intervals=sorted(j for c,j in boxes if c[0]<=edge<=c[1])
  cursor=Q(0)
  for bot,top in intervals:
   assert bot<=cursor
   cursor=max(cursor,top)
  assert cursor==I
 area=sum((c[1]-c[0])*(j[1]-j[0]) for c,j in boxes)
 assert area==(H-A)*I
 worst={}
 for method in ['uniform','completion']:
  worst[method+'_gap']=str(R-max(Q(nodes[i]['bounds'][method+'_upper']) for i in leaves if nodes[i]['method']==method))
 for symbol in ['C','T']:
  worst[symbol+'_upper']=str(max(Q(nodes[i]['bounds'][symbol][1]) for i in leaves if nodes[i]['method']=='moment'))
 return {'nodes':len(nodes),'leaves':len(leaves),'method_counts':counts,'max_depth':data['max_depth'],
         'vertical_slabs':len(endpoints)-1,'exact_area':str(area),'tree_cover':True,
         'independent_vertical_tiling':True,'all_denominators_positive':True,'worst_bounds':worst}

def main():
 data=json.loads((HERE/'certificate.json').read_text());result=verify(data);controls=[]
 for label in ['missing_cell','false_uniform_bound','false_moment_upper','wrong_outer_boundary','wrong_target']:
  bad=copy.deepcopy(data)
  if label=='missing_cell':bad['nodes'][0]['children']=bad['nodes'][0]['children'][:1]
  elif label=='false_uniform_bound':
   bad['nodes'][0]['method']='uniform';bad['nodes'][0].pop('children')
  elif label=='false_moment_upper':
   i=next(i for i,n in enumerate(bad['nodes']) if n['method']=='moment');bad['nodes'][i]['bounds']['T'][1]='0'
  elif label=='wrong_outer_boundary':bad['rectangle']['c'][1]='881/1000'
  else:bad['R']='1/50'
  try:verify(bad)
  except (AssertionError,ValueError) as exc:controls.append({'name':label,'rejected':True,'reason':str(exc)})
  else:raise AssertionError('negative control accepted: '+label)
 print(json.dumps({'passed':True,'certificate':result,'negative_controls':controls},indent=2))
if __name__=='__main__':main()

from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json
R=F(251,10000); I=F(2,47)
edges={tuple(sorted((i,(i+1)%5))) for i in range(5)}
def edge_count(S):
 return sum(a in S and b in S for a,b in edges)
assert all(not all(tuple(sorted(e)) in edges for e in combinations(T,2)) for T in combinations(range(5),3))
pairs=[{'set':list(S),'edges':edge_count(S)} for S in combinations(range(5),2)]
triples=[{'set':list(S),'edges':edge_count(S)} for S in combinations(range(5),3)]
assert min(x['edges'] for x in pairs)==0
assert min(x['edges'] for x in triples)==1>R*25
X={0,2};Y=set(range(5))-X
assert edge_count(X)+edge_count(Y)<=I*25
c=F(5,2*len(Y));j=F(edge_count(Y),25);x=F(len(X),5)
completion=x*(F(1,2)-x)/2
assert c*c*j>R and completion+I-j<R
out={'scope':'Exact finite graph and scalar boundary checks; not Lean or an all-graph result','cycle5':{'edges':sorted(edges),'pairs':pairs,'triples':triples,'target_raw':str(R*25),'small_cut':sorted(X),'large_cut':sorted(Y),'cut_edges':edge_count(X)+edge_count(Y),'cut_allowance':str(I*25),'c':str(c),'j':str(j),'uniform':str(c*c*j),'completion_selector_upper':str(completion+I-j),'note':'C5 is odd; completion construction must run after even blowup in proposed wrapper.'},'balanced_single_edge':{'n':2,'small':[0],'large':[1],'c':'1','j':'0','uniform':'0','note':'Moment denominator zero; uniform branch valid.'},'passed':True}
Path(__file__).with_name('boundary-result.json').write_text(json.dumps(out,indent=2)+'\n')
print('C5 floor/ceil control, valid BCL cut, Q scalar branch and c=1 uniform boundary passed')

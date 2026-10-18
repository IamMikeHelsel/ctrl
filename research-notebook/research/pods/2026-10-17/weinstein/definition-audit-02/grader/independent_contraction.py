"""Independent exact reduction. Does not import the analyst's Clifford model.

Uses words, adjacent swaps, and cancellation rather than bit-mask products.
Checks every independent pair-symmetric coordinate and the curvature basis.
"""
from collections import defaultdict
from itertools import combinations, permutations
from math import comb
import json

N=14
EPS=(1,)*7+(-1,)*7
PAIRS=tuple(combinations(range(N),2))

def product(word):
    word=list(word); sign=1
    # Bubble-sort words, then contract equal adjacent generators.
    for stop in range(len(word)-1,0,-1):
        for j in range(stop):
            if word[j]>word[j+1]:
                word[j],word[j+1]=word[j+1],word[j]
                sign=-sign
    out=[]; j=0
    while j<len(word):
        if j+1<len(word) and word[j]==word[j+1]:
            sign*=EPS[word[j]];j+=2
        else:
            out.append(word[j]);j+=1
    return tuple(out),sign

def clean(x):return {k:v for k,v in x.items() if v}

def expand(weights):
    out={}
    for (p,q),val in weights.items():
        for first,second in set(((p,q),(q,p))):
            a,b=first;c,d=second
            for key,sgn in [((a,b,c,d),1),((b,a,c,d),-1),
                            ((a,b,d,c),-1),((b,a,d,c),1)]:
                assert key not in out
                out[key]=sgn*val
    return out

def contractions(R):
    ordered=defaultdict(int);sortedK=defaultdict(int)
    tb=defaultdict(int);td=defaultdict(int)
    ric=[[0]*N for _ in range(N)]
    for (a,b,c,d),v in R.items():
        if a==c:ric[b][d]+=EPS[a]*v
        coeff=EPS[a]*EPS[b]*EPS[c]*EPS[d]*v
        word,s=product((a,b,c,d));ordered[word]+=s*coeff
        if a<b and c<d:
            sortedK[word]+=s*coeff
            word,s=product((c,d,a,b));sortedK[word]+=s*coeff
        if b==c:
            word,s=product((a,d));tb[word]+=s*coeff*EPS[b]
        if b==d:
            word,s=product((a,c));td[word]+=s*coeff*EPS[b]
    scal=sum(EPS[b]*ric[b][b] for b in range(N))
    assert ric==list(map(list,zip(*ric)))
    assert clean(ordered)==clean({k:2*v for k,v in sortedK.items()})
    assert clean(tb)==({():-scal} if scal else {})
    assert clean(td)==({():scal} if scal else {})
    return clean(sortedK),scal

def expected(weights,scal):
    out={():-scal} if scal else {}
    for a,b,c,d in combinations(range(N),4):
        x=weights.get(((a,b),(c,d)),0)
        y=weights.get(((a,c),(b,d)),0)
        z=weights.get(((a,d),(b,c)),0)
        q=4*EPS[a]*EPS[b]*EPS[c]*EPS[d]*(x-y+z)
        if q:out[(a,b,c,d)]=q
    return out

def run():
    counts={'pair_symmetric':0,'intersecting':0,'disjoint':0,'curvature_basis':0}
    # Every coordinate in Sym^2(Lambda^2), including all non-Bianchi cases.
    for i,p in enumerate(PAIRS):
        for q in PAIRS[i:]:
            weights={(p,q):1};R=expand(weights)
            K,scal=contractions(R)
            assert K==expected(weights,scal)
            counts['pair_symmetric']+=1
            if set(p).intersection(q):
                assert K==({():-scal} if scal else {})
                counts['intersecting']+=1;counts['curvature_basis']+=1
            else:counts['disjoint']+=1
    for a,b,c,d in combinations(range(N),4):
        x=((a,b),(c,d));y=((a,c),(b,d));z=((a,d),(b,c))
        for weights in ({x:1,y:1},{y:1,z:1}):
            K,scal=contractions(expand(weights));assert K=={} and scal==0
            counts['curvature_basis']+=1
    assert counts=={'pair_symmetric':4186,'intersecting':1183,'disjoint':3003,'curvature_basis':3185}
    # The block [x,y,z] has Bianchi row [1,-1,1]. The two claimed
    # vectors [1,1,0] and [0,1,1] form a basis of its kernel.
    # Their x,z coordinates are the two standard unit vectors.
    assert N*N*(N*N-1)//12==counts['curvature_basis']
    # The 4-form fixture has pair coordinates (x,y,z)=(1,-1,1).
    neg={((0,1),(2,3)):1,((0,2),(1,3)):-1,((0,3),(1,2)):1}
    K,scal=contractions(expand(neg));assert K=={(0,1,2,3):12} and scal==0
    # A nonzero scalar fixture prevents normalization errors.
    K,scal=contractions(expand({((0,1),(0,1)):1}))
    assert K=={():-2} and scal==2
    # Gamma_0123 is a unit: its square equals +1 in four positive directions.
    unit_word,unit_sign=product((0,1,2,3,0,1,2,3))
    assert unit_word==() and unit_sign==1
    out={'status':'pass','arithmetic':'Python integers; independent adjacent-swap word reduction',
         'counts':counts,'sorted_K_is_half_ordered_contraction':True,
         'unrestricted_pair_symmetric_grade4_remainder_verified':True,
         'scalar_reduction_for_all_curvature_basis_vectors':True,
         'ricci_symmetry_and_two_diagonal_contractions_verified':True,
         'negative_control':{'scalar':0,'K_gamma0123_coefficient':12,'gamma0123_square':1},
         'normalization_control':{'R0101':1,'scalar':2,'K_scalar':-2}}
    print(json.dumps(out,indent=2))
if __name__=='__main__':run()

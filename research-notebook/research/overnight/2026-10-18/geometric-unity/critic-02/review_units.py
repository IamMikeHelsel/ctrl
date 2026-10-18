"""Independent exact ordered-wedge checks of signs, factors and all matrix units.
No import from either builder or critic-01. Integers and tuples only.
"""
from pathlib import Path
import json
B=Path(__file__).resolve().parent
n=7
subsets=[tuple(i for i in range(n) if m&(1<<i)) for m in range(2**n)]
index={s:i for i,s in enumerate(subsets)}

def creator(i,term):
    s,k=term
    if not k or i in s:return (),0
    new=tuple(sorted((i,)+s));return new,k*(-1 if new.index(i)%2 else 1)

def annihilator(i,term):
    s,k=term
    if not k or i not in s:return (),0
    return tuple(j for j in s if j!=i), k*(-1 if s.index(i)%2 else 1)

def vacuum(term,reverse_factor=False):
    # A product acts from the right. The fixed order is reversed at application.
    for i in reversed(range(n)):
        term=creator(i,annihilator(i,term)) if reverse_factor else annihilator(i,creator(i,term))
    return term

def create_word(s,term):
    for i in reversed(s):term=creator(i,term)
    return term

def contract_word(s,term,wrong_order=False):
    # Reversed written annihilator product acts in increasing index order.
    for i in reversed(s) if wrong_order else s:term=annihilator(i,term)
    return term

def equal_term(a,b):
    return a[1]==b[1] and (not a[1] or a[0]==b[0])

operator_tests=0
for s in subsets:
    term=(s,1)
    assert equal_term(vacuum(term),((),1) if not s else ((),0))
    assert equal_term(vacuum(vacuum(term)),vacuum(term))
    for i in range(n):
        c=creator(i,term);a=annihilator(i,term)
        sign=-1 if sum(k<i for k in s)%2 else 1
        assert equal_term(c,((),0) if i in s else (tuple(sorted(s+(i,))),sign))
        assert equal_term(a,(tuple(k for k in s if k!=i),sign) if i in s else ((),0))
        assert equal_term(creator(i,c),((),0))
        assert equal_term(annihilator(i,a),((),0))
        ac=annihilator(i,c);ca=creator(i,a)
        assert ac[1]+ca[1]==1 and (ac[0] if ac[1] else ca[0])==s
        operator_tests+=5

# Precompute actual contractions, then apply the actual vacuum and creation.
# This still tests every ordered triple I,J,T, including every off-diagonal zero.
contractions={(j,t):contract_word(j,(t,1)) for j in subsets for t in subsets}
unit_checks=0
for i in subsets:
    assert equal_term(create_word(i,((),1)),(i,1))
    for j in subsets:
        for t in subsets:
            got=create_word(i,vacuum(contractions[j,t]))
            want=(i,1) if j==t else ((),0)
            assert equal_term(got,want),(i,j,t,got,want)
            unit_checks+=1

# Arbitrary dense integer operator with no symmetry: verify the proposed double
# coefficient sum's indexing through its action on all 128 input basis vectors.
A=[[((7*i+11*j)%17)-8 for j in range(128)] for i in range(128)]
for t in range(128):
    recovered=[0]*128
    for j in range(128):
        for i in range(128):
            got=create_word(subsets[i],vacuum(contractions[subsets[j],subsets[t]]))
            if got[1]:recovered[index[got[0]]]+=A[i][j]*got[1]
    assert recovered==[A[i][t] for i in range(128)]
assert any(A[i][j]!=A[j][i] for i in range(128) for j in range(128))

negatives={
 'insertion_sign':creator(3,((0,5),1)),
 'erasure_sign':annihilator(3,((0,3,5),1)),
 'unreversed_annihilator_order':vacuum(contract_word((2,5),((2,5),1),wrong_order=True)),
 'reversed_vacuum_factor_on_empty':vacuum(((),1),reverse_factor=True),
 'reversed_vacuum_factor_on_full':vacuum((tuple(range(n)),1),reverse_factor=True),
}
assert negatives['insertion_sign']==((0,3,5),-1)
assert negatives['erasure_sign']==((0,5),-1)
assert negatives['unreversed_annihilator_order']==((),-1)
assert negatives['reversed_vacuum_factor_on_empty'][1]==0
assert negatives['reversed_vacuum_factor_on_full']==(tuple(range(n)),1)

# The actual gamma convention is G+=a+c, G-=c-a. Their difference is 2a.
# Verify the missing-half witness on a created vacuum without floating point.
t=creator(2,((),1));a=annihilator(2,t);c=creator(2,t)
missing_half_coefficient=(a[1]+c[1])-(c[1]-a[1])
assert missing_half_coefficient==2

result={'status':'PASS','arithmetic':'Python exact integers and ordered tuples','dimension':128,'basis_operator_checks':operator_tests,'matrix_unit_triples_checked':unit_checks,'dense_integer_operator_columns_checked':128,'negative_controls':negatives,'missing_half_gives':missing_half_coefficient,'boundary':'Independent finite sign/index check only. The universal actual-basis theorem and algebra equivalence are verified separately by Lean.'}
(B/'units-review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

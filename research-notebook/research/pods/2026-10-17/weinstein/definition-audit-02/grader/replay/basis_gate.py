"""Exact complete-basis check of the declared candidate's algebraic identities.

The 3185 inputs are a basis of algebraic curvature tensors in dimension 14.
This is reproducible finite algebra evidence, not a Lean proof or GU validation.
See candidate-ledger.txt for the basis argument and downstream limits.
"""
from fractions import Fraction as F
from itertools import combinations
import hashlib
import json
from exact_candidate import Model, G, IM, scalar, add_term


def r_from_pairs(weights):
    def R(a,b,c,d):
        if a == b or c == d:
            return 0
        p,q=tuple(sorted((a,b))),tuple(sorted((c,d)))
        key=tuple(sorted((p,q)))
        return weights.get(key,0)*(1 if a<b else -1)*(1 if c<d else -1)
    return R


def generators(model):
    pairs=model.pairs
    for i,p in enumerate(pairs):
        for q in pairs[i:]:
            if set(p)&set(q):
                yield ('intersecting',p,q),{tuple(sorted((p,q))):1}
    for a,b,c,d in combinations(range(model.n),4):
        x=((a,b),(c,d)); y=((a,c),(b,d)); z=((a,d),(b,c))
        yield ('four',a,b,c,d,'xy'),{x:1,y:1}
        yield ('four',a,b,c,d,'yz'),{y:1,z:1}


def canonical(form):
    return [(e,c,v.out()) for (e,c),v in sorted(form.items())]


def main():
    model=Model([1]*7+[-1]*7)
    p1,p2=model.phi(1),model.phi(2)
    count=0
    digest=hashlib.sha256()
    nonzero_ricci=0
    zero_ricci=0
    failure=[]
    for tag,weights in generators(model):
        R=r_from_pairs(weights)
        curv=model.curvature(R)
        ric=model.ricci(R)
        scal=sum(model.signs[a]*ric[a][a] for a in range(model.n))
        ricform=model.sharp_form(ric)
        first=model.prod(p1,model.hodge(curv),'comm')
        inner=model.hodge(model.prod(p2,model.hodge(curv),'J'))
        second=model.hodge(model.prod(p1,inner,'J'))
        candidate=dict(first)
        for k,v in second.items(): add_term(candidate,k,-F(1,2)*v)
        expected_first={k:-2*v for k,v in model.hodge(ricform).items()}
        expected_inner={} if not scal else {(0,0):IM*scal}
        expected=dict(expected_first)
        for k,v in model.hodge(p1).items(): add_term(expected,k,scal*v)
        ok=(first==expected_first and inner==expected_inner and candidate==expected
            and model.skew(first) and model.skew(inner) and model.skew(second))
        if not ok: failure.append(tag)
        count+=1
        if ricform: nonzero_ricci+=1
        else: zero_ricci+=1
        digest.update(json.dumps([tag,canonical(curv),canonical(candidate)],separators=(',',':')).encode())
        digest.update(b'\n')
    # Negative controls: the exact branch choices in (9.3) matter.
    const=r_from_pairs({(p,p):model.signs[p[0]]*model.signs[p[1]] for p in model.pairs})
    curv=model.curvature(const)
    branch_table=[]
    expected_g=model.hodge(p1)
    for first_kind in ['comm','J']:
        for inner_kind in ['comm','J']:
            for outer_kind in ['comm','J']:
                first=model.prod(p1,model.hodge(curv),first_kind)
                inner=model.hodge(model.prod(p2,model.hodge(curv),inner_kind))
                second=model.hodge(model.prod(p1,inner,outer_kind))
                out=dict(first)
                for k,v in second.items(): add_term(out,k,-F(1,2)*v)
                k=next(iter(expected_g))
                coefficient=out.get(k,G())*expected_g[k]
                assert out=={key:coefficient*v for key,v in expected_g.items() if coefficient*v}
                branch_table.append({'first':first_kind,'inner':inner_kind,'outer':outer_kind,
                                     'constant_curvature_multiple_of_S_Phi1':coefficient.out(),
                                     'matches_Einstein_normalization':coefficient==scalar(156)})
    result={'status':'pass' if not failure and count==3185 else 'FAIL',
            'arithmetic':'Gaussian rationals', 'signature':[7,7],
            'basis_dimension':count,'dimension_formula':'n^2(n^2-1)/12 at n=14',
            'basis_vectors_with_zero_ricci':zero_ricci,
            'basis_vectors_with_nonzero_ricci':nonzero_ricci,
            'note':'Zero-Ricci basis vectors are not a full basis of the Weyl subspace. The tested factorization through Ricci is the kernel argument.',
            'failures':failure,'ordered_input_output_sha256':digest.hexdigest(),
            'constant_curvature_branch_table':branch_table}
    print(json.dumps(result,indent=2))
    assert result['status']=='pass'


if __name__=='__main__':main()

"""Exact 128-dimensional real Fock realization, stored as signed permutations.

The Hermitian form K is real symmetric with signature (64,64). Scalar
conjugation is needed when extending the adjoint from R to C.
"""
import hashlib
import json

N=128
IDENTITY=tuple((a,1) for a in range(N))


def mul(a,b):
    return tuple((a[j][0],s*a[j][1]) for j,s in b)


def scale(a,s):
    return tuple((j,s*t) for j,t in a)


def transpose(a):
    out=[None]*N
    for col,(row,s) in enumerate(a):out[row]=(col,s)
    return tuple(out)


def gamma(j,negative):
    return tuple((mask^(1<<j),(-1)**((mask&((1<<j)-1)).bit_count()) *
                  (-1 if negative and mask&(1<<j) else 1)) for mask in range(N))


def main():
    gs=[gamma(j,False) for j in range(7)]+[gamma(j,True) for j in range(7)]
    K=IDENTITY
    for a in range(7,14):K=mul(K,gs[a])
    anticommuting=all(mul(gs[a],gs[b])==scale(mul(gs[b],gs[a]),-1)
                     for a in range(14) for b in range(a+1,14))
    squares=all(mul(gs[a],gs[a])==scale(IDENTITY,1 if a<7 else -1) for a in range(14))
    skew=all(mul(transpose(gs[a]),K)==scale(mul(K,gs[a]),-1) for a in range(14))
    trace=sum(s for col,(row,s) in enumerate(K) if row==col)
    data={'dimension':N,'clifford_signature':[7,7],
          'gamma_squares_correct':squares,'distinct_generators_anticommute':anticommuting,
          'K_definition':'gamma_7 gamma_8 ... gamma_13',
          'K_real_symmetric':transpose(K)==K,'K_square_identity':mul(K,K)==IDENTITY,
          'K_trace':trace,'K_signature':[64,64] if trace==0 and transpose(K)==K and mul(K,K)==IDENTITY else None,
          'all_generators_K_skew_adjoint':skew,
          'adjoint_on_complex_matrices':'A -> K^{-1} conjugate_transpose(A) K',
          'scalar_conjugation_required':True,
          'ordered_generators_and_K_sha256':hashlib.sha256(json.dumps([gs,K],separators=(',',':')).encode()).hexdigest()}
    data['status']='pass' if all((squares,anticommuting,skew,data['K_real_symmetric'],data['K_square_identity'],trace==0)) else 'FAIL'
    print(json.dumps(data,indent=2))
    assert data['status']=='pass'


if __name__=='__main__':main()

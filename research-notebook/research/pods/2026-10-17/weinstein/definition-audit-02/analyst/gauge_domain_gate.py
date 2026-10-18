"""A fixed Weyl subspace and its gauge transport are different domains."""
from fractions import Fraction as F
import json
from exact_candidate import Model, diagonal_R, add_term


def main():
    m=Model([1]*7+[-1]*7)
    R=diagonal_R({(0,1):1,(2,3):1,(0,2):-1,(1,3):-1})
    W=m.curvature(R)
    # h=gamma_0 gamma_1, h^2=-1, h^{-1}=-h.
    def gauge(form):
        out={}
        for (e,c),v in form.items():
            mid,s=m.clifford(3,c)
            end,t=m.clifford(mid,3)
            out[e,end]=-s*t*v
        return out
    def op(p1,p2,X):
        a=m.prod(p1,m.hodge(X),'comm')
        b=m.hodge(m.prod(p1,m.hodge(m.prod(p2,m.hodge(X),'J')),'J'))
        out=dict(a)
        for k,v in b.items():add_term(out,k,-F(1,2)*v)
        return out
    base=op(m.phi(1),m.phi(2),W)
    fixed=op(gauge(m.phi(1)),gauge(m.phi(2)),W)
    moved=op(gauge(m.phi(1)),gauge(m.phi(2)),gauge(W))
    # S(theta^4)=theta^(0,1,2,3,5,...,13), because epsilon_4=+1.
    witness=(m.top^(1<<4),1<<4)
    result={'h':'gamma_0 gamma_1', 'h_square':list(m.clifford(3,3)),
            'h_inverse':'-gamma_0 gamma_1',
            'h_is_Spin_element_reason':'product of two orthogonal positive unit vectors',
            'weyl_fixture_nonzero_independent_entries':{'R0101':1,'R2323':1,'R0202':-1,'R1313':-1},
            'ricci':m.ricci(R), 'at_identity_zero':not base,
            'rotated_phi_fixed_W_zero':not fixed,
            'rotated_phi_rotated_W_zero':not moved,
            'fixed_W_nonzero_component':{'exterior_basis':'S(theta^4)','clifford_basis':'gamma_4',
                                        'coefficient':fixed[witness].out()},
            'fixed_W_nonzero_term_count':len(fixed),
            'status':'pass' if not base and fixed and not moved else 'FAIL'}
    print(json.dumps(result,indent=2))
    assert result['status']=='pass'


if __name__=='__main__':main()

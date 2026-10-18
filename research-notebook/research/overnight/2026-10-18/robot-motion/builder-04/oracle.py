"""Independent exact polynomial-to-Bernstein fixture generator.
It is a builder test, not independent acceptance of the builder's proof.
"""
from fractions import Fraction as F
from pathlib import Path
from math import comb
import json, random
HERE=Path(__file__).resolve().parent
WEIGHTS=[1,-4,6,-4,1]
def val(h,es,t):
    return sum(d*sum(w*max(t-tau-k*h,F(0))**3 for k,w in enumerate(WEIGHTS))/(6*h**4) for tau,d in es)
def coeffs(h,c,es):
    ps=sorted({c}|{tau+k*h for tau,_ in es for k in range(5) if tau+k*h>=c})
    out=[val(h,es,t) for t in ps];cells=[]
    for L,R in zip(ps,ps[1:]):
        width=R-L
        power=[F(0)]*4
        for tau,delta in es:
            for k,w in enumerate(WEIGHTS):
                root=tau+k*h
                if root<=L:
                    for j in range(4):
                        power[j]+=delta*w*comb(3,j)*(L-root)**(3-j)*width**j/(6*h**4)
                else: assert R<=root
        b=[sum(power[j]*F(comb(i,j),comb(3,j)) for j in range(i+1)) for i in range(4)]
        assert b[0]==val(h,es,L) and b[3]==val(h,es,R)
        for u in [F(0),F(1,4),F(1,2),F(3,4),F(1)]:
            assert sum(comb(3,i)*(1-u)**(3-i)*u**i*b[i] for i in range(4))==val(h,es,L+width*u)
        out+=b
        cells.append({'left':str(L),'right':str(R),'power':[str(x) for x in power],'bernstein':[str(x) for x in b]})
    return max([abs(x) for x in out]+[F(0)]),cells

def lean(x):return f'({x.numerator}/{x.denominator})'
def main():
    rng=random.Random(2026101804)
    histories=[(F(1),F(0),[]),(F(1),F(0),[(F(0),F(1)),(F(1),F(-1))]),
        (F(1),F(0),[(F(0),F(1)),(F(1,4),F(-1))]),
        (F(1),F(0),[(F(0),F(1)),(F(1,4),F(-1)),(F(1,2),F(0)),(F(3,4),F(0))]),
        (F(1,5),F(13,25),[(F(11,50),F(1,50)),(F(31,50),F(-1,50))]),
        (F(1),F(-1),[(F(10),F(-1)),(F(-2),F(1)),(F(10),F(1))])]
    for _ in range(54):
        h=rng.choice([F(1,2),F(1),F(2)])
        c=rng.choice([F(-1),F(0),F(1,3),F(1),F(3,2),F(6)])
        es=[(F(rng.randrange(-4,13),4),F(rng.randrange(-3,4),3)) for _ in range(rng.randrange(1,6))]
        histories.append((h,c,es))
    rows=[]; lines=['import VelocityFixtures','namespace RobotMotion.VelocityAdmission','set_option maxRecDepth 100000','set_option maxHeartbeats 0']
    for h,c,es in histories:
        bound,cells=coeffs(h,c,es)
        for V in [bound,bound*F(9,10),F(0)]:
            expected=bound<=V
            idx=len(rows)
            rows.append({'id':idx,'h':str(h),'c':str(c),'events':[[str(a),str(d)] for a,d in es],
                'V':str(V),'coefficient_max':str(bound),'expected':expected,'cells':cells})
            ev='['+','.join(f'({lean(a)},{lean(d)})' for a,d in es)+']'
            lines.append(f'theorem oracle_{idx:03d} : checkVelocity {lean(h)} {lean(V)} {lean(c)} {ev} = {str(expected).lower()} := by decide +kernel')
    lines+=['end RobotMotion.VelocityAdmission','']
    (HERE/'VelocityOracle.lean').write_text('\n'.join(lines))
    (HERE/'oracle-cases.json').write_text(json.dumps({'seed':2026101804,'scope':'Exact finite coefficient decisions; no optimality or hardware claim.', 'cases':rows},indent=2)+'\n')
    print(json.dumps({'histories':len(histories),'decisions':len(rows),'pass':sum(r['expected'] for r in rows)}))
if __name__=='__main__':main()

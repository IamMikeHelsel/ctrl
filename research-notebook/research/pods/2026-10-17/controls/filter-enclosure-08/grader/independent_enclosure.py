"""Independent rational variation-of-constants enclosures in physical coordinates.

No builder functions, numerical states, floating arithmetic, or numerical library
are used. Exact finite 4x4 transition matrices are applied to boxes once per
phase. Polynomial forcing has a separately bounded integrated-series tail.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
from datetime import datetime, timezone
import hashlib, json

G=Path(__file__).resolve().parent
B=G.parent/'builder'
REF=G.parent.parent/'causal-stop-05/builder/reference.json'
EXPECTED='b284178e77f8cf2bda67d4ee9ec29583b4b87a53a32cd9b6d8c54e8ff7b94cb8'
DIGITS=90
GRID=10**DIGITS
TARGET=F(1,10**75)
P=[[F(x) for x in row] for row in [[0,10,0,0],[0,0,10,0],[0,0,-80,80],[-160,-120,-10,-20]]]

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def integrity():
    assert sha(B/'artifact-sha256.json')==EXPECTED
    hashes=json.loads((B/'artifact-sha256.json').read_text())
    for name,d in hashes.items(): assert sha(B/name)==d,name
    return {**hashes,'artifact-sha256.json':EXPECTED,'reference.json':sha(REF)}

def deriv(p): return [F(i)*p[i] for i in range(1,len(p))] or [F(0)]
def value(p,t):
    r=F(0)
    for c in reversed(p): r=r*t+c
    return r
def coeff(p,i): return p[i] if i<len(p) else F(0)
def vector_norm(v): return max(abs(x) for x in v)
def mvec(a,v): return [sum((x*y for x,y in zip(row,v)),F(0)) for row in a]
def mmul(a,b): return [[sum((a[i][k]*b[k][j] for k in range(4)),F(0)) for j in range(4)] for i in range(4)]
def ceil_fraction(x): return -((-x.numerator)//x.denominator)
def round_box(lo,hi,grid=GRID):
    return F((lo*grid).numerator//(lo*grid).denominator,grid),F(ceil_fraction(hi*grid),grid)
def decimal(x,digits):
    s=10**digits
    assert (x*s).denominator==1
    n=int(x*s);sign='-' if n<0 else '';n=abs(n)
    return sign+str(n//s)+'.'+str(n%s).zfill(digits)

def physical_forcing(q,k):
    v=deriv(q);a=deriv(v);j=deriv(a)
    L=len(q)
    # z=(x,v/10,a/100,u/100), all physical states retained at each join.
    out=[]
    for i in range(L):
        out.append([F(0),F(0),F(1,125) if i==0 else F(0),
                    160*coeff(q,i)+12*coeff(v,i)+F(3,10)*coeff(a,i)+k*coeff(j,i)/5])
    return out

def remainder(N,a,d,box,forcing):
    assert a < N+2
    B0=max(max(abs(lo),abs(hi)) for lo,hi in box)
    power=a**(N+1)
    initial=B0*power/F(factorial(N+1))/(1-a/F(N+2))
    forced=[]
    for ell,g in enumerate(forcing):
        forced.append(vector_norm(g)*factorial(ell)*d**(ell+1)*power /
                      F(factorial(N+ell+2))/(1-a/F(N+ell+3)))
    return initial+sum(forced,F(0)),initial,forced

def propagate(box,q,k,d):
    M=[[d*x for x in row] for row in P]
    a=max(sum(abs(x) for x in row) for row in M)
    forcing=physical_forcing(q,k)
    N=max(1,a.numerator//a.denominator)
    while True:
        tail,initial_tail,forcing_tails=remainder(N,a,d,box,forcing)
        if tail<=TARGET: break
        N+=1
        assert N<1200
    ident=[[F(i==j) for j in range(4)] for i in range(4)]
    E=[row[:] for row in ident];term=[row[:] for row in ident]
    # For g_ell*t^ell, integration gives ell!*d^(ell+1)*M^n/(n+ell+1)!.
    fterms=[[d**(ell+1)*x/F(ell+1) for x in g] for ell,g in enumerate(forcing)]
    forced=[sum((v[i] for v in fterms),F(0)) for i in range(4)]
    for n in range(1,N+1):
        term=[[x/n for x in row] for row in mmul(M,term)]
        E=[[E[i][j]+term[i][j] for j in range(4)] for i in range(4)]
        fterms=[[x/F(n+ell+1) for x in mvec(M,v)] for ell,v in enumerate(fterms)]
        forced=[forced[i]+sum((v[i] for v in fterms),F(0)) for i in range(4)]
    out=[]
    for i in range(4):
        lower=forced[i]-tail;upper=forced[i]+tail
        for c,(lo,hi) in zip(E[i],box):
            lower+=min(c*lo,c*hi);upper+=max(c*lo,c*hi)
        out.append(round_box(lower,upper))
    rec={'duration':str(d),'degree':N,'homogeneous_norm':str(a),
         'tail_bound':str(tail),'initial_tail':str(initial_tail),
         'forcing_tails':[str(x) for x in forcing_tails],
         'input_box':[[str(x) for x in b] for b in box],
         'output_box':[[str(x) for x in b] for b in out]}
    return out,rec

def check_reference(phases):
    previous=None;end=F(0);count=0
    for phase in phases:
        assert F(phase['start'])==end
        q=list(map(F,phase['position_coefficients_local_time']))
        polys=[q]
        for _ in range(3):polys.append(deriv(polys[-1]))
        if previous is None: assert [value(p,F(0)) for p in polys]==[0,0,0,10]
        else:
            assert [value(p,F(0)) for p in polys]==previous
            count+=4
        duration=F(phase['end'])-F(phase['start']);assert duration>0
        previous=[value(p,duration) for p in polys];end=F(phase['end'])
    assert previous==[F(3,5),0,0,0] and end==F(3,2)
    return count

def error_matrix_from_physical(q,k):
    # Derive y=z-r with r=(q,q'/10,q''/100,q''/100).
    v=deriv(q);a=deriv(v)
    r=[q,[x/10 for x in v],[x/100 for x in a],[x/100 for x in a]]
    dr=list(map(deriv,r));g=physical_forcing(q,k)
    forcing=[]
    for ell in range(max(len(q),4)):
        pc=mvec(P,[coeff(p,ell) for p in r])
        forcing.append([coeff([gg[i] for gg in g],ell)+pc[i]-coeff(dr[i],ell) for i in range(4)])
    assert all(x==0 for f in forcing[4:] for x in f)
    mat=[[F(0) for _ in range(8)] for _ in range(8)]
    for i in range(4):
        mat[i][:4]=P[i]
        for ell in range(4):mat[i][4+ell]=forcing[ell][i]
    for ell in range(1,4):mat[4+ell][3+ell]=F(ell)
    return mat

def audit_primary_certificate(phases,cert):
    assert cert['reference_sha256']==sha(REF)
    assert cert['source_sha256']==sha(B/'enclose.py')
    scale=10**cert['scale_decimal_digits'];checked=0
    for case in cert['cases']:
        state=[(0,0)]*4;k=F(case['k']);witness=F(case['witness_time']);reached=F(0)
        for phase,rec in zip(phases,case['phases']):
            start=F(phase['start']);d=min(F(phase['end']),witness)-start
            assert rec['phase']==phase['name'] and F(rec['start'])==reached==start and F(rec['dt'])==d
            q=list(map(F,phase['position_coefficients_local_time']))
            expected=error_matrix_from_physical(q,k)
            actual=[list(map(F,row)) for row in rec['matrix']]
            assert actual==expected
            initial=[tuple(map(int,b)) for b in rec['initial_grid_intervals']]
            assert initial==state+[(scale,scale),(0,0),(0,0),(0,0)]
            a=max(sum(abs(d*x) for x in row) for row in actual)
            B0=F(max(max(abs(lo),abs(hi)) for lo,hi in initial),scale)
            N=rec['last_degree'];assert N+1==rec['terms'] and a<N+2
            tail=B0*a**(N+1)/F(factorial(N+1))/(1-a/F(N+2))
            pad=ceil_fraction(tail*scale)
            assert F(rec['matrix_infinity_norm_times_dt'])==a
            assert F(rec['initial_norm_bound'])==B0
            assert tail<=F(cert['tail_target'])
            assert int(rec['tail_grid_units'])==pad and F(rec['tail_bound_upper'])==F(pad,scale)
            end=[tuple(map(int,b)) for b in rec['end_grid_intervals']]
            assert all(lo<=hi for lo,hi in end)
            state=end[:4];reached=start+d;checked+=1
        assert reached==witness
        result=case['position_error_enclosure_m']
        assert F(result['lower'])<=F(state[0][0],scale)<=F(state[0][1],scale)<=F(result['upper'])
        assert F(result['upper'])-F(result['lower'])==F(result['width'])==F(1,10**15)
        assert F(result['lower'])>F(1,5000)
    return checked

def run_case(name,k,witness,phases,claimed):
    box=[(F(0),F(0)) for _ in range(4)];records=[];reached=F(0)
    for phase in phases:
        start=F(phase['start']);end=F(phase['end'])
        if start>=witness:break
        assert start==reached
        d=min(witness,end)-start;q=list(map(F,phase['position_coefficients_local_time']))
        box,record=propagate(box,q,k,d)
        record.update({'phase':phase['name'],'start':str(start)})
        records.append(record);reached=start+d
        print(name,phase['name'],'degree',record['degree'],flush=True)
    assert reached==witness
    error=(box[0][0]-value(q,d),box[0][1]-value(q,d))
    displayed=round_box(*error,grid=10**15)
    assert displayed==(F(claimed['lower']),F(claimed['upper']))
    assert error[0]>F(1,5000)
    return {'law':name,'k':str(k),'time':str(witness),'error_interval':[str(x) for x in error],
            'displayed_interval':[decimal(x,15) for x in displayed],
            'strict_margin_lower':str(error[0]-F(1,5000)),'phases':records}

def counterchecks():
    # Exhaustive small signed-rational interval images. Compare to exact vertices.
    count=0
    for n in range(-7,8):
      for d in range(1,8):
       c=F(n,d)
       for lo in range(-4,5):
        for hi in range(lo,5):
         a,b=min(c*lo,c*hi),max(c*lo,c*hi)
         got=round_box(a,b,grid=10)
         assert got[0]<=a<=b<=got[1];count+=1
    # Rounding toward zero misses a negative endpoint; positive-only interval
    # ordering misses a negative multiplier. These are intentional bad controls.
    x=F(-1,3);assert F(int(x*10),10)>x
    assert F(-2)*F(-1)>F(-2)*F(3)
    # A scalar geometric tail majorant must exceed an explicit finite tail.
    a=F(5,2);N=8
    bound=a**(N+1)/F(factorial(N+1))/(1-a/F(N+2))
    finite=sum((a**j/F(factorial(j)) for j in range(N+1,N+31)),F(0))
    assert finite<bound
    return {'signed_interval_images_checked':count,'bad_rounding_and_order_controls_rejected':True,
            'finite_scalar_tail_below_majorant':True}

def main():
    before=integrity();(G/'hashes-before.json').write_text(json.dumps(before,indent=2)+'\n')
    phases=json.loads(REF.read_text());cert=json.loads((B/'enclosure.json').read_text())
    joins=check_reference(phases);primary=audit_primary_certificate(phases,cert)
    expected=[('filtered_original',F(5,480),F(171,400)),('filtered_compensated',F(29,480),F(1581,2000))]
    cases=[]
    for (name,k,t),claim in zip(expected,cert['cases']):
        assert name==claim['law'] and k==F(claim['k']) and t==F(claim['witness_time'])
        cases.append(run_case(name,k,t,phases,claim['position_error_enclosure_m']))
    checks=counterchecks();after=integrity();assert after==before
    (G/'hashes-after.json').write_text(json.dumps(after,indent=2)+'\n')
    result={'accepted':True,'method':'exact rational 4x4 transition series and polynomial variation of constants; explicit separate remainder bounds; one box rounding per phase',
            'coordinates':'physical x,v/10,a/100,u/100','rounding_digits':DIGITS,'tail_target':str(TARGET),
            'source_sha256':sha(Path(__file__)),'reference_sha256':sha(REF),
            'reference_derivative_join_checks':joins,'primary_phase_certificates_audited':primary,
            'counterchecks':checks,'cases':cases,
            'scope':'Validated numerical enclosures under the stated classical ODE and exact reference; no Lean proof of the program or ODE-exponential bridge.'}
    (G/'independent-enclosures.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'accepted':True,'intervals':[c['displayed_interval'] for c in cases]},indent=2),flush=True)

if __name__=='__main__':main()

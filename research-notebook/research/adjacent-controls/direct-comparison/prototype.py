#!/usr/bin/env python3
"""Exact-rational interval prototype, NOT a Lean-checked theorem.

No floating-point operation contributes to a safety comparison. Endpoints are
integers divided by 2**44; operations round outwards. The Taylor bounds and
interval rules are mathematical assumptions of this Python implementation,
not new imported Lean lemmas. Only the standard library is required.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import argparse, hashlib, json, math, platform, sys, time

D = 2**44
P50 = ((380,514,250),(514,1319,769),(250,769,556))
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]

def floor(q): return q.numerator // q.denominator
def ceil(q): return -floor(-q)

class I:
    def __init__(self, lo, hi=None):
        self.lo, self.hi = lo, lo if hi is None else hi
        assert self.lo <= self.hi
    @classmethod
    def rational(cls, lo, hi=None):
        hi = lo if hi is None else hi
        return cls(floor(F(lo)*D), ceil(F(hi)*D))
    def __add__(self, b): return I(self.lo+b.lo,self.hi+b.hi)
    def __neg__(self): return I(-self.hi,-self.lo)
    def __sub__(self,b): return self+-b
    def __mul__(self,b):
        values = [a*c for a in (self.lo,self.hi) for c in (b.lo,b.hi)]
        return I(min(values)//D, -((-max(values))//D))
    def clip(self): return I(max(-D,min(D,self.lo)),max(-D,min(D,self.hi)))
    def serial(self): return [self.lo,self.hi]

def coefficients_at(r,h):
    """E=e^-rh, B=int_0^h e^-rs ds, C=int_0^h (h-s)e^-rs ds.
    The even partial sums through n=12 are upper bounds; adding negative
    n=13 is a lower bound. Alternating terms decrease when 0<=r*h<=1.
    E, B, C each decrease in r by their integral representations.
    """
    assert 0 <= r*h <= 1
    answer=[]
    for k in (0,1,2):
        upper=sum(((-r)**n*h**(n+k)/math.factorial(n+k) for n in range(13)),F(0))
        lower=upper+(-r)**13*h**(13+k)/math.factorial(13+k)
        answer.append((lower,upper))
    return answer

def coefficients(lo,hi,h):
    left,right=coefficients_at(lo,h),coefficients_at(hi,h)
    return tuple(I.rational(right[k][0],left[k][1]) for k in range(3))

def parts(lo,hi,n): return [(lo+(hi-lo)*F(k,n),lo+(hi-lo)*F(k+1,n)) for k in range(n)]
def energy_upper(z):
    # P is positive definite (exact LDL check below). A convex quadratic on
    # an axis-aligned box attains a maximum at a vertex. This is NOT a claim
    # that checking original-state corners suffices for a nonlinear trajectory.
    return F(max(sum(v[i]*P50[i][j]*v[j] for i in range(3) for j in range(3))
                 for v in product(*[(q.lo,q.hi) for q in z])),50*D*D)

def ldlt():
    p=[[F(x,50) for x in row] for row in P50]
    l=[[F(i==j) for j in range(3)] for i in range(3)]; d=[]
    for i in range(3):
        d.append(p[i][i]-sum(l[i][k]**2*d[k] for k in range(i)))
        assert d[-1]>0
        for j in range(i+1,3):
            l[j][i]=(p[j][i]-sum(l[j][k]*l[i][k]*d[k] for k in range(i)))/d[i]
    assert all(p[i][j]==sum(l[i][k]*d[k]*l[j][k] for k in range(3)) for i in range(3) for j in range(3))
    return [str(q) for q in d]

def run(n,nr,h,steps):
    started=time.monotonic(); one=I(D); hh=I.rational(h); halfh2=I.rational(h*h/2)
    initial=[parts(F(99,100),F(101,100),n),parts(F(49,100),F(51,100),n),parts(F(-1,100),F(1,100),n)]
    rates=parts(F(9,10),F(11,10),nr)
    aggregate=[{'energy_upper':F(0),'position_low_tick':10*D,'position_high_tick':-10*D} for _ in range(steps)]
    cells=[]; coeff_trace=[]
    for ri,(rlo,rhi) in enumerate(rates):
        e,b,c=coefficients(rlo,rhi,h)
        coeff_trace.append({'rate':[str(rlo),str(rhi)],'E':e.serial(),'B':b.serial(),'C':c.serial()})
        for ii,bounds in enumerate(product(*initial)):
            z=tuple(I.rational(*bound) for bound in bounds); trace=[]
            for k in range(steps):
                u=(-(z[0]+I.rational(3)*z[1]+I.rational(2)*z[2])).clip()
                # Every actual a remains in [-1,1]: initial a in [-.01,.01]
                # and each exact actuator segment is a convex mix of a,u.
                # Thus x(s)=x(0)+s*v(0)+int_0^s(s-q)*a(q)dq gives these
                # bounds simultaneously for ALL 0<=s<=h, not sampled offsets.
                pathlo=z[0].lo+min(0,(hh*z[1]).lo)-halfh2.hi
                pathhi=z[0].hi+max(0,(hh*z[1]).hi)+halfh2.hi
                nxt=(z[0]+hh*z[1]+c*z[2]+(halfh2-c)*u,
                     z[1]+b*z[2]+(hh-b)*u,e*z[2]+(one-e)*u)
                ev=energy_upper(nxt)
                a=aggregate[k];a['energy_upper']=max(a['energy_upper'],ev)
                a['position_low_tick']=min(a['position_low_tick'],pathlo)
                a['position_high_tick']=max(a['position_high_tick'],pathhi)
                trace.append({'command':u.serial(),'next_state':[q.serial() for q in nxt],
                              'path_position':[pathlo,pathhi]})
                z=nxt
            cells.append({'rate_cell':ri,'initial_cell':ii,'initial_box':[[str(a),str(b)] for a,b in bounds],'steps':trace})
    summaries=[]
    for k,a in enumerate(aggregate):
        summaries.append({'sample_time':str((k+1)*h),'energy_upper_exact':str(a['energy_upper']),
          'energy_upper_approx':float(a['energy_upper']),
          'preceding_whole_segment_position_exact':[str(F(a['position_low_tick'],D)),str(F(a['position_high_tick'],D))],
          'preceding_whole_segment_position_approx':[a['position_low_tick']/D,a['position_high_tick']/D],
          'all_cells_energy_le_12':a['energy_upper']<=12,
          'all_cells_segment_travel_le_2':a['position_low_tick']>=-2*D and a['position_high_tick']<=2*D})
    return {'partition':{'each_state_coordinate':n,'rate_cells':nr,'total_parameter_boxes':n**3*nr},
      'hold':str(h),'steps':steps,'terminal_time':str(steps*h),'duration_seconds':time.monotonic()-started,
      'terminal_energy_certified_by_prototype':summaries[-1]['all_cells_energy_le_12'],
      'whole_prefix_travel_certified_by_prototype':all(q['all_cells_segment_travel_le_2'] for q in summaries),
      'per_sample_summary':summaries,'rate_coefficients':coeff_trace,'trace':cells}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--subdivisions',type=int,default=4);ap.add_argument('--rate-cells',type=int,default=16)
    ap.add_argument('--hold',default='1/10');ap.add_argument('--steps',type=int,default=13)
    ap.add_argument('--output',default='prototype-results.json');args=ap.parse_args()
    assert args.subdivisions>0 and args.rate_cells>0 and args.steps>0
    h=F(args.hold);assert 0<h<=F(1,5)
    d=ldlt();run_data=run(args.subdivisions,args.rate_cells,h,args.steps)
    sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
    output={'status':'exact-rational interval prototype; not a Lean proof; no formal replay',
      'model':"x'=v; v'=a; a'=r*(u-a); u=clip(-x-3v-2a,-1,1) held each sample; fixed unknown r in [.9,1.1]",
      'error_scope':'zero errors throughout finite prefix; existing robust invariant may apply after proved entry, but the composition is not formalized here',
      'coverage':'full closed initial box [.99,1.01] x [.49,.51] x [-.01,.01] and full rate interval; Cartesian rational partitions cover all points, not just original corners',
      'arithmetic':'all decision arithmetic uses integers/Fraction; interval endpoints are ticks/2**44; outward floor/ceil multiplication; decimals for display only',
      'analytic_basis':'alternating Taylor terms n0..12 upper and n0..13 lower at r endpoints for E,B,C, monotone decreasing in r; exact held-flow coefficient identity; acceleration convexity; integrated acceleration path bound; positive definite quadratic is convex',
      'trust_boundary':'Python implementation and unformalized analytic basis remain trusted. Trace supports review/regeneration, not independent proof checking by Lean.',
      'P_times_50':P50,'P_ldl_positive_diagonal':d,'tick_denominator':D,
      'python':platform.python_version(),'prototype_sha256':sha(Path(__file__)),
      'invocation':[sys.executable,*sys.argv],
      'model_source_sha256':{n:sha(ROOT/'lean-controls/LeanControls'/n) for n in ['UncertainLag.lean','UncertainTravel.lean']},
      'run':run_data,
      'utility':'If these bounds pass and are formally checked, the original feedback can reach the same invariant from the same box. The recovery maneuver then demonstrates a proof method/domain extension, not an unsafe-baseline rescue or necessarily better performance.',
      'recovery_comparison':{'terminal_time':'5/4','checked_Lean_terminal_bound':'V<=12',
        'checked_Lean_path_bound':['657/800','5297/3200'],
        'fair_comparison':'Hold1/20 with25steps shares terminal time and zero-error prefix with recovery; recovery holds u=-1 without prefix updates. Both may use the same post-entry sample clock. This is not identical prefix timing freedom, and interval bound tightness is not measured controller performance.',
        'cost_boundary':'Python propagation duration is reported; no Lean proof production or replay cost exists for this direct-feedback prototype. It must not be compared as equivalent to recovery Lean check cost.'},
      'title_ideas':['From an Initial Box to a Verified Travel Bound','Two Paths into a Safe Region','Checking the Safety of Sampled Control with Actuator Lag'],
      'next_gate':'Independently validate interval rules/Taylor bounds and port/check the full-box prefix trace in Lean before calling the baseline safe by formal proof. Do not expand the recovery claim to superiority.'}
    (HERE/args.output).write_text(json.dumps(output,separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in run_data.items() if k not in ('trace','rate_coefficients')},indent=2))
if __name__=='__main__':main()

from pathlib import Path
from fractions import Fraction as F
from itertools import product
from functools import lru_cache
import json,csv,mpmath as mp
mp.mp.dps=80
HERE=Path(__file__).resolve().parent
SOURCE=HERE.parent/'forced-screen-03'
M=lambda f:mp.mpf(F(f).numerator)/F(f).denominator
controllers={'original':F(5,48),'lag_compensated_changed':F(29,48)}
rates=['r80','r100','r120','r80_120_80']
ws={'w0':F(0),'wplus':F(1,100),'wminus':F(-1,100)}
jerks=['plus_to_half','plus_minus_zero']
expected={'__'.join(p)for p in product(controllers,rates,ws,jerks)}
with (SOURCE/'summary.csv').open() as f:summary={r['case']:r for r in csv.DictReader(f)}
assert set(summary)==expected and len(summary)==48
@lru_cache(None)
def physical_step(r,w,j,k,dt):
    g3=M(r)*M(w)-M(j)
    g4=(20*M(k)/10-1)*M(j)
    # Independently assembled physical system, without normalized coordinates.
    B=mp.matrix([[0,1,0,0,0],[0,0,1,0,0],[0,0,-r,r,g3],[-16000,-1200,-10,-20,g4],[0,0,0,0,0]])
    return mp.expm(B*M(dt),method='pade')
def physical_at(name,t):
    controller,rc,wc,jc=name.split('__'); k=controllers[controller];w=ws[wc]
    H=F(1,2)if jc=='plus_to_half'else F(1)
    cuts=sorted(set([F(0),H]+([F(1,8),F(3,8)]if rc=='r80_120_80'else[])+([F(1,4),F(1,2)]if jc=='plus_minus_zero'else[])))
    y=mp.matrix([0,0,0,0,1]);q=[F(0)]*3
    for a,b in zip(cuts,cuts[1:]):
        if t<a:break
        end=min(t,b); dt=end-a
        r=(120 if F(1,8)<=a<F(3,8)else 80)if rc=='r80_120_80'else int(rc[1:])
        j=10 if jc=='plus_to_half'or a<F(1,4)else(-10 if a<F(1,2)else 0)
        y=physical_step(r,str(w),j,str(k),str(dt))*y
        q=[q[0]+q[1]*dt+q[2]*dt**2/2+j*dt**3/6,q[1]+q[2]*dt+j*dt**2/2,q[2]+j*dt]
        if t<=b:return y,q
    raise AssertionError(t)
records=[];rows_count=0;boundary_count=0;max_boundary=0.;max_peak_difference=mp.mpf(0);counts={k:0 for k in controllers}
for name in sorted(expected):
    with (SOURCE/'traces'/(name+'.csv')).open() as f:rows=list(csv.DictReader(f))
    rows_count+=len(rows)
    peak=max(rows,key=lambda r:abs(float(r['ex_m'])))
    assert float(peak['ex_m'])==float(summary[name]['ex_m_sampled_max_abs']) or -float(peak['ex_m'])==float(summary[name]['ex_m_sampled_max_abs'])
    y,q=physical_at(name,F(peak['t_s']))
    diff=abs(y[0]-M(peak['ex_m']));max_peak_difference=max(max_peak_difference,diff)
    assert diff<mp.mpf('1e-14'),(name,diff)
    within=abs(y[0])<=M(F(1,5000))
    assert within==(summary[name]['within_position_target_at_samples']=='True')
    counts[name.split('__')[0]]+=bool(within)
    for left,right in zip(rows,rows[1:]):
        if left['t_s']!=right['t_s']:continue
        assert left['event_side']=='left' and right['event_side']=='right'
        boundary_count+=1
        fields=['ex_m','ev_m_per_s','ea_m_per_s2','b_m_per_s2','q0_m','q1_m_per_s','q2_m_per_s2','x_m','v_m_per_s','a_m_per_s2','u_m_per_s2']
        err=max(abs(float(left[k])-float(right[k]))for k in fields);max_boundary=max(max_boundary,err);assert err<1e-12
        k=float(controllers[name.split('__')[0]])
        dj=float(right['reference_jerk_m_per_s3'])-float(left['reference_jerk_m_per_s3'])
        du_star=float(right['u_star_m_per_s2'])-float(left['u_star_m_per_s2'])
        du_prime=float(right['u_prime_m_per_s3'])-float(left['u_prime_m_per_s3'])
        dr=float(right['r_per_s'])-float(left['r_per_s'])
        da_prime=float(right['actual_jerk_m_per_s3'])-float(left['actual_jerk_m_per_s3'])
        assert abs(du_star-k*dj/10)<1e-12
        assert abs(du_prime-20*k*dj/10)<1e-11
        assert abs(da_prime-dr*(float(left['u_m_per_s2'])+float(left['w_m_per_s2'])-float(left['a_m_per_s2'])))<1e-11
    records.append({'case':name,'time_s':peak['t_s'],'physical_position_error_80_digits_m':mp.nstr(y[0],70),'difference_from_saved_peak_m':mp.nstr(diff,25),'within_target_at_max_saved_position_sample':bool(within)})
assert rows_count==72120 and boundary_count==72 and counts=={'original':0,'lag_compensated_changed':20}
out={'passed':True,'independent_method':'80-digit physical-coordinate 5x5 affine matrix exponential using Pade; no imported builder helpers or normalized matrix. Each recorded position-peak time independently propagated from zero. All traces independently inspected for event continuity/jump identities.','mpmath_version':mp.__version__,'case_count':48,'rows_inspected':rows_count,'position_peak_samples_reproduced':48,'max_position_peak_difference_m':mp.nstr(max_peak_difference,25),'within_target_counts':counts,'boundaries_checked':boundary_count,'max_boundary_residual':max_boundary,'cases':records,'scope':'Independent numerical samples, not interval enclosures or a uniform theorem.'}
(HERE/'physical-review.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items()if k not in ['cases','independent_method']},indent=2))

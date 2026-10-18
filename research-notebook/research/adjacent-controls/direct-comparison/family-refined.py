#!/usr/bin/env python3
"""Predeclared all-box interval comparison; no Lean proof or safety inference on failure."""
from pathlib import Path
from itertools import product
import hashlib,json,platform,time
import prototype as p

HERE=Path(__file__).resolve().parent
PLAN={
 'center':['1','1/2','0'],'coordinate_halfwidth':'lambda/100',
 'lambda_values':[1,2,4,8],'controllers':['direct','backup'],
 'hold':'1/20','steps':25,'terminal_time':'5/4','rate':['9/10','11/10'],
 'state_subdivisions_per_coordinate':8,'rate_cells':32,'parameter_boxes_per_run':16384,
 'tick_denominator':p.D,'errors':'zero throughout each tested finite prefix; no tail simulated',
 'refinement':'one uniform refinement authorized after coarse run: state8 per coordinate,rate32,both policies,all four predetermined lambda values; no further tuning',
 'pass_rule':'terminal energy upper<=12 AND every prefix position enclosure lies in [-2,2]',
 'failure_rule':'an enclosure failed; no claim of an unsafe trajectory or impossibility',
 'volume':'(lambda/50)^3; geometric initial-state volume, not probability',
 'comparison':'same box, rate interval, .05 hold grid, 25 steps, and interval arithmetic. Backup holds -1 throughout; direct samples clip(-x-3v-2a). Backup split into 25 identical-command segments for equal propagation structure.'}

def ratio(q):return {'exact':str(q),'approx':float(q)}
def run(lam,mode):
 start=time.monotonic();F=p.F;I=p.I;D=p.D
 half=F(lam,100);center=(F(1),F(1,2),F(0));h=F(1,20)
 boxes=[p.parts(c-half,c+half,8)for c in center];rates=p.parts(F(9,10),F(11,10),32)
 one=I(D);hh=I.rational(h);hh2=I.rational(h*h/2);three=I.rational(3);two=I.rational(2)
 # All initial accelerations are in [-1,1], and all commands stay in [-1,1].
 assert half<=1
 steps=[{'energy':F(0),'xmin':10*D,'xmax':-10*D}for _ in range(25)]
 cells=[];digest=hashlib.sha256()
 for ri,(lo,hi)in enumerate(rates):
  e,b,c=p.coefficients(lo,hi,h)
  for ii,bounds in enumerate(product(*boxes)):
   z=tuple(I.rational(*q)for q in bounds);low=10*D;high=-10*D
   for k in range(25):
    u=I(-D)if mode=='backup'else(-(z[0]+three*z[1]+two*z[2])).clip()
    vlo=(hh*z[1]).lo;vhi=(hh*z[1]).hi
    xlo=z[0].lo+min(0,vlo)-hh2.hi;xhi=z[0].hi+max(0,vhi)+hh2.hi
    z=(z[0]+hh*z[1]+c*z[2]+(hh2-c)*u,z[1]+b*z[2]+(hh-b)*u,e*z[2]+(one-e)*u)
    ev=p.energy_upper(z);a=steps[k]
    a['energy']=max(a['energy'],ev);a['xmin']=min(a['xmin'],xlo);a['xmax']=max(a['xmax'],xhi)
    low=min(low,xlo);high=max(high,xhi)
    trace=[ri,ii,k,u.serial(),[q.serial()for q in z],[xlo,xhi],str(ev)]
    digest.update((json.dumps(trace,separators=(',',':'))+'\n').encode())
   cells.append({'rate_cell':ri,'initial_cell':ii,'terminal_state_ticks':[q.serial()for q in z],
      'terminal_energy_upper':str(ev),'whole_prefix_position_ticks':[low,high]})
 terminal=steps[-1]['energy'];low=min(q['xmin']for q in steps);high=max(q['xmax']for q in steps)
 energy_ok=terminal<=12;path_ok=low>=-2*D and high<=2*D
 return {'lambda':lam,'controller':mode,'initial_box':[[str(c-half),str(c+half)]for c in center],
  'volume':ratio(F(lam,50)**3),'relative_volume_to_lambda1':lam**3,
  'terminal_energy_upper':ratio(terminal),
  'whole_prefix_position':[ratio(F(low,D)),ratio(F(high,D))],
  'terminal_enclosure_pass':energy_ok,'path_enclosure_pass':path_ok,
  'combined_enclosure_pass':energy_ok and path_ok,
  'first_sample_with_all_cells_energy_le_12':next((str((k+1)*h)for k,a in enumerate(steps)if a['energy']<=12),None),
  'python_generation_seconds':time.monotonic()-start,'trace_sha256':digest.hexdigest(),
  'trace_hash_format':'UTF-8 compact JSON lines [rate_index,initial_index,step_index,command_ticks,state_ticks,path_position_ticks,energy_upper_fraction_string]; canonical traversal rate,Cartesian state,step; recomputed by this script',
  'per_sample':[{'time':str((k+1)*h),'energy_upper':str(a['energy']),'preceding_segment_position_ticks':[a['xmin'],a['xmax']]}for k,a in enumerate(steps)],
  'cells':cells}

def main():
 sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
 plan_text=json.dumps(PLAN,sort_keys=True,separators=(',',':'))
 output={'status':'predeclared; not yet run','plan':PLAN,'plan_sha256':hashlib.sha256(plan_text.encode()).hexdigest(),
   'plan_recorded_before_runs_unix_seconds':time.time(),
   'sources':{n:sha(HERE/n)for n in ('family.py','family-refined.py','prototype.py')},'python':platform.python_version(),
   'trust_boundary':'Exact rational decision arithmetic in Python. Taylor monotonicity, interval arithmetic, convex quadratic maximization, and path reasoning are not checked by Lean here. No formal replay or physical validation.',
   'cost_boundary':'Reported costs are Python interval generation only; not proof elaboration/kernel checking and not controller runtime.',
   'interpretation':'Bounds measure certificate conservatism as well as trajectories. Different bounds do not establish control performance superiority. A failure does not establish a violation.'}
 target=HERE/'family-refined-results.json'
 target.write_text(json.dumps(output,indent=2)+'\n')
 assert json.loads(target.read_text())['plan_sha256']==output['plan_sha256']
 output['P_ldl_positive_diagonal']=p.ldlt()
 output['runs']=[run(lam,mode)for lam in PLAN['lambda_values']for mode in PLAN['controllers']]
 output['status']='completed; all-box rational interval prototype, not Lean-checked'
 output['finished_unix_seconds']=time.time()
 target.write_text(json.dumps(output,separators=(',',':'))+'\n')
 print(json.dumps([{k:r[k]for k in ('lambda','controller','volume','terminal_energy_upper','whole_prefix_position','combined_enclosure_pass','python_generation_seconds')}for r in output['runs']],indent=2))
if __name__=='__main__':main()

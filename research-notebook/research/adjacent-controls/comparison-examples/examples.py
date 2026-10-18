#!/usr/bin/env python3
"""Six preselected numerical illustrations. No proof and no parameter search."""
from pathlib import Path
import hashlib,html,importlib.util,json,platform,time

HERE=Path(__file__).resolve().parent
SOURCE=HERE.parent/'recovery-proof/experiment.py'
spec=importlib.util.spec_from_file_location('existing_experiment',SOURCE)
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
CASES=[
 {'id':'rest','title':'At rest at the target','z':[0,0,0],'r':1,'reason':'Control case: no motion is required.'},
 {'id':'slow','title':'Slow motion, already near the target','z':[.5,.05,0],'r':1,'reason':'Tests the effort cost of an unnecessary fixed backup.'},
 {'id':'nominal','title':'The current nominal example','z':[1,.5,0],'r':1,'reason':'Center of the proved initial box.'},
 {'id':'toward','title':'Already moving toward the target','z':[1,-.5,0],'r':1,'reason':'Tests a backup whose fixed direction may be unhelpful.'},
 {'id':'fast','title':'Faster approach, slower actuator','z':[1,.9,.2],'r':.9,'reason':'Positive initial acceleration with the slowest admitted rate.'},
 {'id':'near_limit','title':'Fast approach close to the limit','z':[1.5,1,.3],'r':.9,'reason':'Stress case outside the proved initial box; tests limits of both policies.'}]
H=.05;T=1.25;END=10.;DT=.01

def effort(z0,r,mode):
 z=tuple(z0);now=0.;l1=l2=0.
 if mode=='backup_handoff':z=m.flow(z,-1.,T,r);now=T;l1=l2=T
 start=now;n=0
 while now<END-1e-12:
  end=min(END,start+(n+1)*H);u=m.command(z);dt=end-now
  l1+=abs(u)*dt;l2+=u*u*dt;z=m.flow(z,u,dt,r);now=end;n+=1
 return {'command_absolute_integral':l1,'command_square_integral':l2}

def draw(results):
 W=1280;CW=590;CH=425;top=140
 out=[f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="1500" viewBox="0 0 {W} 1500">',
 '<rect width="1280" height="1500" fill="#f7f5ef"/>',
 '<style>text{font-family:Arial,sans-serif;fill:#21343c}.title{font-size:21px;font-weight:700}.sub{font-size:15px;fill:#53656c}.metric{font-size:14px}.tick{font-size:12px;fill:#53656c}</style>',
 '<text x="50" y="54" font-size="34" font-weight="700">One backup does not fit every start</text>',
 '<text x="50" y="86" class="sub">Preselected numerical examples • exact held-flow formula evaluated in floating point • no safety proof</text>',
 '<text x="50" y="112" class="sub">Zero errors; direct hold h=0.05; backup u=-1 until T=1.25, then the same feedback; horizon 10</text>',
 '<line x1="920" y1="52" x2="966" y2="52" stroke="#087f82" stroke-width="3"/><text x="978" y="57" class="sub">direct</text>',
 '<line x1="1060" y1="52" x2="1106" y2="52" stroke="#ac5900" stroke-width="3" stroke-dasharray="7 4"/><text x="1117" y="57" class="sub">backup</text>']
 for idx,case in enumerate(results):
  x=50+(idx%2)*620;y=top+(idx//2)*(CH+20)
  out.append(f'<rect x="{x}" y="{y}" width="{CW}" height="{CH}" rx="13" fill="white" stroke="#d6dedc"/>')
  out.append(f'<text x="{x+22}" y="{y+34}" class="title">{html.escape(case["title"])}</text>')
  out.append(f'<text x="{x+22}" y="{y+60}" class="sub">z(0)={case["z"]}; r={case["r"]}</text>')
  px=x+52;py=y+85;pw=510;ph=210
  X=lambda t:px+t/END*pw
  Y=lambda q:py+(4-q)/8*ph
  for v in (-2,0,2):
   color='#b13c43'if abs(v)==2 else'#bac7ca'
   out.append(f'<line x1="{px}" y1="{Y(v)}" x2="{px+pw}" y2="{Y(v)}" stroke="{color}" stroke-width="1" stroke-dasharray="4 4"/><text x="{px-23}" y="{Y(v)+4}" class="tick">{v}</text>')
  out.append(f'<line x1="{X(T)}" y1="{py}" x2="{X(T)}" y2="{py+ph}" stroke="#6e7880" stroke-dasharray="3 4"/>')
  for t in (0,1.25,5,10):out.append(f'<text x="{X(t)}" y="{py+ph+20}" text-anchor="middle" class="tick">{t:g}</text>')
  out.append(f'<text x="{px}" y="{py-8}" class="tick">position x(t)</text><text x="{px+pw}" y="{py+ph+37}" text-anchor="end" class="tick">normalized time</text>')
  for mode,color,dash in [('direct_feedback','#087f82',''),('backup_handoff','#ac5900','stroke-dasharray="7 4"')]:
   trace=case[mode]['trace'];points=' '.join(f'{X(q["t"]):.3f},{Y(q["x"]):.3f}'for q in trace)
   assert all(-4<=q['x']<=4 for q in trace)
   out.append(f'<polyline points="{points}" fill="none" stroke="{color}" stroke-width="2.8" {dash}/>')
  columns=[22,132,242,352,477]
  for col,label in zip(columns,['Policy','peak |x|','V(T)','command TV','∫ |u| dt']):
   out.append(f'<text x="{x+col}" y="{y+349}" class="metric">{label}</text>')
  for row,mode,label,col in [(0,'direct_feedback','Direct','#087f82'),(1,'backup_handoff','Backup','#ac5900')]:
   a=case[mode]
   values=[label]+[f'{a[k]:.3f}'for k in ('peak_abs_travel','terminal_V','command_total_variation','command_absolute_integral')]
   for xpos,value in zip(columns,values):
    out.append(f'<text x="{x+xpos}" y="{y+373+23*row}" class="metric" style="fill:{col}">{value}</text>')
 out.append('<text x="50" y="1490" class="sub">Dashed horizontal lines: ±2 travel limits. Vertical line: T. All cases shown; a failed numerical case is not a theorem.</text></svg>')
 (HERE/'comparison.svg').write_text('\n'.join(out)+'\n')

def main():
 sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
 result={'status':'predeclared cases, before execution','cases_selected_before_runs':CASES,
  'model':"x'=v; v'=a; a'=r*(u-a); r fixed per run; clip(-x-3v-2a) in[-1,1]",
  'parameters':{'direct_hold':H,'backup_until':T,'common_feedback_hold_after_T':H,'horizon':END,'energy_grid_spacing':DT,'errors':0},
  'scope':'Numerical illustration only. No parameter search, interval certification, Lean proof, or physical validation. Only the nominal center belongs to the currently proved small initial box.',
  'metric_notes':{'peak_abs_travel':'Analytic segment extrema, with velocity roots bisected numerically60 times; not outward-rounded bounds.',
    'terminal_V':'Computed at exactly T1.25 for both policies.',
    'command_total_variation':'Sum of absolute changes between held commands; excludes a jump from an unspecified prehistory command.',
    'command_absolute_integral':'Exact held-command time integral evaluated in floating point; command effort proxy, not physical energy.',
    'post_T_sampled_peak_V':'Numerically sampled; not an all-time assertion.'},
  'source_sha256':{'examples.py':sha(Path(__file__)),'reused_experiment.py':sha(SOURCE)},'python':platform.python_version()}
 target=HERE/'results.json';target.write_text(json.dumps(result,indent=2)+'\n')
 started=time.monotonic();rows=[]
 for case in CASES:
  q=dict(case)
  for mode in('direct_feedback','backup_handoff'):
   q[mode]=m.run(case['z'],case['r'],mode,H,END,DT)
   q[mode].update(effort(case['z'],case['r'],mode))
  q['backup_minus_direct']={k:q['backup_handoff'][k]-q['direct_feedback'][k]for k in('peak_abs_travel','terminal_V','command_total_variation','command_absolute_integral')}
  rows.append(q)
 result.update(status='completed numerical illustration; not proof',runs=rows,seconds=time.monotonic()-started)
 target.write_text(json.dumps(result,indent=2)+'\n');draw(rows)
 print(json.dumps([{'case':r['id'],**{mode:{k:r[mode][k]for k in('peak_abs_travel','terminal_V','command_total_variation','command_absolute_integral','observed_travel_within_2')}for mode in('direct_feedback','backup_handoff')}}for r in rows],indent=2))
if __name__=='__main__':main()

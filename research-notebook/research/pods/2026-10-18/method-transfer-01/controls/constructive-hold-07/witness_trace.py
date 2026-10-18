#!/usr/bin/env python3
"""Binary64 illustration only. The Lean constructor and witness carry the proof."""
from pathlib import Path
import hashlib,json,math
HERE=Path(__file__).resolve().parent
h=1/2000;m=[.14,-.01,-1.17];center=9573033/100000000

def phase(z,r,q):
 e=math.exp(-r*h);one=-math.expm1(-r*h)
 x,v,a=z
 return [x+h*v+q*h*h/2+(a-q)*(h/r-one/(r*r)),v+q*h+(a-q)*one/r,q+(a-q)*e]

def trace(changing):
 nodes=[m,phase(m,8,-1.21)];cells=[]
 for n in range(3):
  reading=m if n==0 else [nodes[n][i]+([.0005,.005,.025][i] if changing else 0) for i in range(3)]
  raw=-8*(reading[0]-center)-6*reading[1]-reading[2]/2
  command=max(-2,min(2,raw));rate=12 if changing and n+1==2 else 8
  delta=.005 if changing and n+1==2 else 0
  end=phase(nodes[n+1],rate,command+delta);nodes.append(end)
  cells.append({'cell':n+1,'start_s':(n+1)*h,'end_s':(n+2)*h,'sample_s':n*h,'reading':reading,'rate':rate,'raw_command':raw,'clipped_command':command,'physical_target_error':delta,'endpoint_x_v_a':end})
 assert abs(cells[0]['clipped_command']-3635533/12500000)<1e-14
 return {'nodes':nodes,'digital_cells':cells,'horizon_s':4*h,'endpoint_x_v_a':nodes[-1]}

out={'status':'binary64 illustration, not an interval certificate or proof','model':'same second-order node recurrence as ConstructiveFlow.node_recurrence','center':center,'pending_rate':8,'pending_target':-1.21,'initial':m,'changing':trace(True),'fixed_rate_zero_noise_baseline':trace(False),'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(HERE.glob('Constructive*.lean'))},'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(HERE/'witness-trace.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k]['endpoint_x_v_a'] for k in ['changing','fixed_rate_zero_noise_baseline']}))

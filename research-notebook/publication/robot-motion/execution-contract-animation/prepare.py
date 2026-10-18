"""Build animation inputs from independently reviewed numerical traces."""
from pathlib import Path
from fractions import Fraction
import csv,gzip,hashlib,json

HERE=Path(__file__).resolve().parent
WORK=HERE.parents[2]
POD=WORK/'research/overnight/2026-10-18/robot-motion'
GATES={
 'builder-03/artifact-sha256.json':'abfc9ca6da02e5cbec77b4019e8f356c80d612f65bea3fcb3e7b227ec1cf6d58',
 'smooth-baseline-01/artifact-sha256-final.json':'25d2b152cfc0890bdbef79870560474a291f4bdf64c9076ca0e034eb7fd3f26f',
 'smooth-review-01/artifact-sha256.json':'cf71b8400b5a301666587e7787ca1aedca8ec219d4cfb116ac24aee48faf7c04',
}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for name,digest in GATES.items():assert sha(POD/name)==digest
methods=[('native_fast','Native fast','#8A9BA8'),('native_matched','Native matched','#E7A144'),
         ('fir_checked','Checked FIR','#6299EA'),('smooth_n90_cap10mm','Smooth / 10 mm cap','#42C6A2')]
output=[];inputs={}
for method,label,color in methods:
 folder=POD/('smooth-baseline-01' if method.startswith('smooth') else 'builder-03')
 trace=folder/'traces'/f'return_generous__{method}__r100__w00__dt500us.csv.gz'
 metrics=folder/'metrics.json';inputs[str(trace.relative_to(WORK))]=sha(trace);inputs[str(metrics.relative_to(WORK))]=sha(metrics)
 with gzip.open(trace,'rt')as f:
  samples=[{'t':float(Fraction(r['time_exact'])),'x_mm':1000*float(r['x'])}for r in csv.DictReader(f)]
 row=next(r for r in json.loads(metrics.read_text())['rows']if r['method']==method and r['case']=='return_generous'and r['rate']==100 and r['disturbance']==0 and r['sample_step_s']==.0005)
 assert row['full_task_pass']
 output.append({'method':method,'label':label,'color':color,'samples':samples,
  'jerk_integral':row['suffix_until_horizon_jerk_energy_m2_s5'],
  'peak_jerk':row['suffix_until_horizon_actual_jerk_peak_m_s3'],
  'extra_travel_mm':1000*row['suffix_until_horizon_extra_forward_excursion_m']})
(HERE/'data.json').write_text(json.dumps({'scope':'Offline generous-task scalar simulation; rate100/s,w0. Actual positions, not reference positions. Animation interpolates saved samples. Planning time omitted.','methods':output},separators=(',',':'))+'\n')
(HERE/'data-provenance.json').write_text(json.dumps({'gates':GATES,'input_hashes':inputs,'data_sha256':sha(HERE/'data.json')},indent=2)+'\n')
print('Four reviewed traces prepared for animation.')

"""Numerical refined-moment scout using C<=0 and C+S<=0. Does not certify a graph or a universal bound."""
import datetime,hashlib,json,math,os,platform
from pathlib import Path
HERE=Path(__file__).resolve().parent
STOP=datetime.datetime(2026,10,18,21,45,tzinfo=datetime.timezone.utc)
I=2/47
TARGETS=[.0256,.0254,.0252,.025,.0248,.0246,.0244,.0242,.024,.0238]

def point(c,j):
 y=1/(2*c);x=1-y
 uniform=c*c*j
 f=1.5*x*x-1.25*x+9/32 if x<=3/8 else x*(.5-x)/2
 completion=f+I-j if c>=.75 else math.inf
 a=min(c,1-c);ell=min(4*a*a,a*(1-a))
 cubic=uniform-64*ell*c**4*j**3
 return y,min(uniform,completion),min(cubic,completion)

def margins(R,y,j):
 mu=2*j/y;b=y-.5
 if b<=0:return math.inf,math.inf
 L=8*R*(y-mu)-2*mu
 C=j-4*R*(y-mu)**2-mu**2
 B=(j-R)/b-L
 S=B*B/4+L*mu-C
 return C,S

rows=[{'target':r,'old_failures':0,'cubic_failures':0,'moment_failures':0,
       'combined_failures':0,'first_combined_failure':None} for r in TARGETS]
worst_old=(-1,None);worst_cubic=(-1,None);cases=0
for ci in range(801):
 if datetime.datetime.now(datetime.timezone.utc)>=STOP:raise SystemExit('Research deadline')
 c=.5+.5*ci/800
 for ji in range(241):
  j=I*ji/240
  y,old,cubic=point(c,j);cases+=1
  if old>worst_old[0]:worst_old=(old,{'c':c,'j':j})
  if cubic>worst_cubic[0]:worst_cubic=(cubic,{'c':c,'j':j})
  for row in rows:
   R=row['target'];C,S=margins(R,y,j)
   old_ok=old<=R;cubic_ok=cubic<=R;moment_ok=C<=0 and C+S<=0
   row['old_failures']+=not old_ok
   row['cubic_failures']+=not cubic_ok
   row['moment_failures']+=not(old_ok or moment_ok)
   if not(cubic_ok or moment_ok):
    row['combined_failures']+=1
    if row['first_combined_failure'] is None:
     row['first_combined_failure']={'c':c,'j':j,'y':y,'C':C,'S':S,'C_plus_S':C+S,'old':old,'cubic':cubic}
# Broad-tangent failure previously certified exactly must survive the scout.
negative=margins(.02586,50/79,I)
assert negative[0]<0<negative[1]
result={'executed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'machine':platform.machine(),'pid':os.getpid(),'cases':cases,'targets':rows,
 'grid_max_old':worst_old,'grid_max_cubic':worst_cubic,
 'negative_broad_tangent':{'C':negative[0],'S':negative[1],'C_plus_S':sum(negative)},
 'criterion':'old or cubic baseline, or C<=0 and C+S<=0',
 'scope':'binary64 scalar grid, not graphs, no universal or novelty conclusion',
 'decision_rule':'Only propose a subsequent exact-cover experiment; zero sampled failures is not proof. A failed sufficient certificate is not a graph counterexample.'}
(HERE/'refined-profile-scout-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

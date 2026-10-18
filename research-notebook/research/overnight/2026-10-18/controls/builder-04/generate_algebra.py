from fractions import Fraction as F
from pathlib import Path
import json
HERE=Path(__file__).resolve().parent
cert=json.loads((HERE/'exact-check.json').read_text());P=[[F(x) for x in row] for row in cert['P']]
def transpose(A):return list(map(list,zip(*A)))
def mm(A,B):return [[sum(a*b for a,b in zip(row,col)) for col in zip(*B)] for row in A]
def ldl(A):
 n=len(A);L=[[F(i==j) for j in range(n)] for i in range(n)];d=[]
 for j in range(n):
  d.append(A[j][j]-sum(L[j][k]**2*d[k] for k in range(j)))
  if d[-1]==0:
   assert all(A[i][j]-sum(L[i][k]*L[j][k]*d[k] for k in range(j))==0 for i in range(j+1,n));continue
  assert d[-1]>0
  for i in range(j+1,n):L[i][j]=(A[i][j]-sum(L[i][k]*L[j][k]*d[k] for k in range(j)))/d[-1]
 return L,d
def lean(x):return f'({x.numerator}/{x.denominator}:ℝ)' if x.denominator!=1 else str(x.numerator)
def sos(A,names):
 L,d=ldl(A);terms=[]
 for k,dk in enumerate(d):
  if dk:
   terms.append(lean(dk)+'*('+ ' + '.join(lean(L[i][k])+'*'+names[i] for i in range(k,len(A)) if L[i][k]) + ')^2')
 return ' +\n      '.join(terms)
text='''module
public import SettlingFixtures
@[expose] public section
noncomputable section
namespace LeanControls.QuadraticHold
open Set
open UncertainLag (State)
open VariableResponse RobustHold ScaledTracking Settling SettlingFixtures
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- This exact rational quadratic is q^T Q^-1 q for the frozen Q. -/
def energy (x y z : ℝ) : ℝ :=
 (49597375*x^2 + 120006000*x*y + 51027750*x*z +
  212058000*y^2 + 113732000*y*z + 102314375*z^2)/68317631

def energyRate (r d x y z : ℝ) : ℝ :=
 ((2*49597375*x +120006000*y+51027750*z)*(40*y) +
 (120006000*x+2*212058000*y+113732000*z)*(40*z) +
 (51027750*x+113732000*y+2*102314375*z)*
 (-r/2*x-3*r/2*y-3*r/2*z+r/2*d))/68317631

'''
def theorem(name,goal,A,names,defs):
 return f'theorem {name} ({" ".join(names)} : ℝ) : {goal} := by\n  calc\n    0 ≤ {sos(A,names)} := by positivity\n    _ = _ := by unfold {defs}; ring\n\n'
text+=theorem('energy_nonneg','0 ≤ energy x y z',P,['x','y','z'],'energy')
for r in (80,120):
 A=[[F(0),40,0],[0,0,40],[-F(r,2),-F(3*r,2),-F(3*r,2)]];PA=mm(P,A);AtP=mm(transpose(A),P);PB=[P[i][2]*F(r,2) for i in range(3)]
 N=[[-PA[i][j]-AtP[i][j]-20*P[i][j] for j in range(3)]+[-PB[i]] for i in range(3)]+[[-b for b in PB]+[F(20)]]
 text+=theorem('endpoint_'+str(r),f'0 ≤ 20*d^2-20*energy x y z-energyRate {r} d x y z',N,['x','y','z','d'],'energy energyRate')
for name,index,coef in [('speed',1,F(259,500)),('acceleration',2,F(81,100))]:
 N=[[coef*P[i][j]-F(i==index and j==index) for j in range(3)] for i in range(3)]
 text+=theorem(name+'_coordinate',f'0 ≤ {lean(coef)}*energy x y z-{["x","y","z"][index]}^2',N,['x','y','z'],'energy')
text+='''theorem dissipation {r d : ℝ} (hlo : 80 ≤ r) (hhi : r ≤ 120)
    (hw : |d| ≤ 1) (x y z : ℝ) :
    energyRate r d x y z ≤ 20*(1-energy x y z) := by
  have hp : 0 ≤ 20*d^2-20*energy x y z-energyRate r d x y z := by
    calc
      0 ≤ ((120-r)/40)*(20*d^2-20*energy x y z-energyRate 80 d x y z) +
          ((r-80)/40)*(20*d^2-20*energy x y z-energyRate 120 d x y z) := by
        exact add_nonneg (mul_nonneg (by linarith) (endpoint_80 x y z d))
          (mul_nonneg (by linarith) (endpoint_120 x y z d))
      _ = _ := by unfold energyRate; ring
  have hab := abs_le.mp hw
  have hd2 : d^2 ≤ 1 := by nlinarith
  nlinarith

theorem initial_energy {x y z : ℝ} (hx : |x| ≤ 16) (hy : |y| ≤ 32)
    (hz : |z| ≤ 64) : energy x y z ≤ 1000000 := by
  have hx2 : x^2 ≤ 256 := by have := abs_le.mp hx; nlinarith
  have hy2 : y^2 ≤ 1024 := by have := abs_le.mp hy; nlinarith
  have hz2 : z^2 ≤ 4096 := by have := abs_le.mp hz; nlinarith
  unfold energy
  nlinarith [sq_nonneg (x-y),sq_nonneg (x-z),sq_nonneg (y-z)]

end LeanControls.QuadraticHold
'''
(HERE/'QuadraticAlgebra.lean').write_text(text)

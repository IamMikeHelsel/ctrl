module
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

theorem energy_nonneg (x y z : ℝ) : 0 ≤ energy x y z := by
  calc
    0 ≤ (49597375/68317631:ℝ)*(1*x + (480024/396779:ℝ)*y + (204111/396779:ℝ)*z)^2 +
      (810000/396779:ℝ)*(1*y + (151/810:ℝ)*z)^2 +
      (100/81:ℝ)*(1*z)^2 := by positivity
    _ = _ := by unfold energy; ring

theorem endpoint_80 (x y z d : ℝ) : 0 ≤ 20*d^2-20*energy x y z-energyRate 80 d x y z := by
  calc
    0 ≤ (1049162500/68317631:ℝ)*(1*x + (172188/83933:ℝ)*y + (1697537/419665:ℝ)*z + (-408222/419665:ℝ)*d)^2 +
      (16023486720000/5734103722723:ℝ)*(1*y + (-1027193477/801174336:ℝ)*z + (-759501739/801174336:ℝ)*d)^2 +
      (175836125/25036698:ℝ)*(1*z + (-576049/1406689:ℝ)*d)^2 +
      (2503780/1406689:ℝ)*(1*d)^2 := by positivity
    _ = _ := by unfold energy energyRate; ring

theorem endpoint_120 (x y z d : ℝ) : 0 ≤ 20*d^2-20*energy x y z-energyRate 120 d x y z := by
  calc
    0 ≤ (2069717500/68317631:ℝ)*(1*x + (1928201/827887:ℝ)*y + (3128385/827887:ℝ)*z + (-612333/827887:ℝ)*d)^2 +
      (168148708317500/56559278575697:ℝ)*(1*y + (-67304588102/67259483327:ℝ)*z + (50814171525/67259483327:ℝ)*d)^2 +
      (473255560000/67259483327:ℝ)*(1*z + (-9877995/23662778:ℝ)*d)^2 +
      (5957780/11831389:ℝ)*(1*d)^2 := by positivity
    _ = _ := by unfold energy energyRate; ring

theorem speed_coordinate (x y z : ℝ) : 0 ≤ (259/500:ℝ)*energy x y z-y^2 := by
  calc
    0 ≤ (102765761/273270524:ℝ)*(1*x + (480024/396779:ℝ)*y + (204111/396779:ℝ)*z)^2 +
      (22801/396779:ℝ)*(1*y + (518/151:ℝ)*z)^2 := by positivity
    _ = _ := by unfold energy; ring

theorem acceleration_coordinate (x y z : ℝ) : 0 ≤ (81/100:ℝ)*energy x y z-z^2 := by
  calc
    0 ≤ (160695495/273270524:ℝ)*(1*x + (480024/396779:ℝ)*y + (204111/396779:ℝ)*z)^2 +
      (656100/396779:ℝ)*(1*y + (151/810:ℝ)*z)^2 := by positivity
    _ = _ := by unfold energy; ring

theorem dissipation {r d : ℝ} (hlo : 80 ≤ r) (hhi : r ≤ 120)
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

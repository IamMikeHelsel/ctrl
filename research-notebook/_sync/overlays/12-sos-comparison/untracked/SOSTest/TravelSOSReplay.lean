import SOS
open CPoly
set_option maxHeartbeats 2000000
namespace TravelSOSComparison
namespace TravelQuarterLower
noncomputable def residual (h x v a : ℝ) : ℝ :=
    ((-19 / 160) * h ^ 3 + (-5 / 16) * h ^ 2 + (241 / 200) * h + (3 / 2)) * x ^ 2 +
    ((-57 / 80) * h ^ 3 + (1 / 40) * h ^ 2 + (33 / 5) * h + (-1 / 100)) * x * v +
    ((-19 / 40) * h ^ 3 + (7 / 100) * h ^ 2 + (22 / 5) * h) * x * a +
    ((-171 / 160) * h ^ 3 + (231 / 80) * h ^ 2 + (271 / 200) * h + (151 / 100)) * v ^ 2 +
    ((-57 / 40) * h ^ 3 + (401 / 100) * h ^ 2 + (69 / 50) * h + (3 / 50)) * v * a +
    ((-19 / 40) * h ^ 3 + (139 / 100) * h ^ 2 + (-69 / 25) * h + (8 / 5)) * a ^ 2
theorem residual_nonnegative (h x v a : ℝ) (hlo : 0 ≤ h) (hhi : h ≤ (1 / 5)) :
    0 ≤ residual h x v a := by
  unfold residual
  sos_witness { sigmas := [
    ([0], { terms := [
        (((4741 / 200) : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (5 : ℚ) * CMvPolynomial.X 0) * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 1 + CMvPolynomial.C ((645 / 4741) : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((40 / 431) : ℚ) * CMvPolynomial.X 3)),
        (((5586379 / 237050) : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (5 : ℚ) * CMvPolynomial.X 0) * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((199287 / 5586379) : ℚ) * CMvPolynomial.X 3)),
        (((5867327189 / 279318950) : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (5 : ℚ) * CMvPolynomial.X 0) * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 3)),
        (((34551 / 160) : ℚ), CMvPolynomial.X 0 * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 1 + CMvPolynomial.C ((4351 / 11517) : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((2930 / 11517) : ℚ) * CMvPolynomial.X 3)),
        (((787660 / 3839) : ℚ), CMvPolynomial.X 0 * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((9173 / 196915) : ℚ) * CMvPolynomial.X 3)),
        (((9692417 / 78766) : ℚ), CMvPolynomial.X 0 * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 3))] }),
    ([1], { terms := [
        (((15 / 2) : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (5 : ℚ) * CMvPolynomial.X 0) * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 1 + CMvPolynomial.C ((-1 / 300) : ℚ) * CMvPolynomial.X 2)),
        (((90599 / 12000) : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (5 : ℚ) * CMvPolynomial.X 0) * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((1800 / 90599) : ℚ) * CMvPolynomial.X 3)),
        (((724522 / 90599) : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (5 : ℚ) * CMvPolynomial.X 0) * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 3)),
        (((9939 / 16) : ℚ), CMvPolynomial.X 0 * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 1 + CMvPolynomial.C ((2611 / 9939) : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((2938 / 16565) : ℚ) * CMvPolynomial.X 3)),
        (((24074951 / 39756) : ℚ), CMvPolynomial.X 0 * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((5333616 / 120374755) : ℚ) * CMvPolynomial.X 3)),
        (((10790881255 / 24074951) : ℚ), CMvPolynomial.X 0 * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 3))] })] }
noncomputable def energy (x v a : ℝ) : ℝ := ((38 / 5)) * x ^ 2 + ((514 / 25)) * x * v + (10) * x * a + ((1319 / 50)) * v ^ 2 + ((769 / 25)) * v * a + ((278 / 25)) * a ^ 2
noncomputable def nextX (h x v a : ℝ) : ℝ := ((-1 / 8) * h ^ 2 + 1) * x + ((-3 / 8) * h ^ 2 + 1 * h) * v + ((-1 / 4) * h ^ 2) * a
noncomputable def nextV (h x v a : ℝ) : ℝ := (0) * x + (1) * v + (1 * h) * a
noncomputable def nextA (h x v a : ℝ) : ℝ := ((-1 / 4) * h) * x + ((-3 / 4) * h) * v + ((-3 / 2) * h + 1) * a
theorem residual_identity (h x v a : ℝ) :
    energy x v a - energy (nextX h x v a) (nextV h x v a) (nextA h x v a) -
      h * (x^2 + v^2 + a^2) = h * residual h x v a := by
  unfold energy nextX nextV nextA residual
  ring
theorem interval_decrease (h x v a : ℝ) (hlo : 0 ≤ h) (hhi : h ≤ (1 / 5)) :
    energy (nextX h x v a) (nextV h x v a) (nextA h x v a) ≤ energy x v a - h * (x^2+v^2+a^2) := by
  have hp := mul_nonneg hlo (residual_nonnegative h x v a hlo hhi)
  have hi := residual_identity h x v a
  linarith
#print axioms TravelSOSComparison.TravelQuarterLower.residual_nonnegative
#print axioms TravelSOSComparison.TravelQuarterLower.residual_identity
#print axioms TravelSOSComparison.TravelQuarterLower.interval_decrease
end TravelQuarterLower
namespace TravelQuarterUpper
noncomputable def residual (h x v a : ℝ) : ℝ :=
    ((-21 / 100) * h ^ 3 + (-11 / 50) * h ^ 2 + (9 / 200) * h + (3 / 2)) * x ^ 2 +
    ((-63 / 50) * h ^ 3 + (-29 / 50) * h ^ 2 + (87 / 25) * h + (-1 / 100)) * x * v +
    ((-43 / 20) * h ^ 3 + (77 / 50) * h ^ 2 + (-293 / 100) * h) * x * a +
    ((-189 / 100) * h ^ 3 + (6 / 25) * h ^ 2 + (487 / 200) * h + (151 / 100)) * v ^ 2 +
    ((-129 / 20) * h ^ 3 + (73 / 50) * h ^ 2 + (243 / 100) * h + (3 / 50)) * v * a +
    ((-181 / 25) * h ^ 3 + (172 / 25) * h ^ 2 + (-249 / 50) * h + (8 / 5)) * a ^ 2
theorem residual_nonnegative (h x v a : ℝ) (hlo : 0 ≤ h) (hhi : h ≤ (1 / 5)) :
    0 ≤ residual h x v a := by
  unfold residual
  sos_witness { sigmas := [
    ([0], { terms := [
        (((4509 / 200) : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (5 : ℚ) * CMvPolynomial.X 0) * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 1 + CMvPolynomial.C ((37 / 501) : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((-293 / 4509) : ℚ) * CMvPolynomial.X 3)),
        (((208433 / 8350) : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (5 : ℚ) * CMvPolynomial.X 0) * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((88837 / 1250598) : ℚ) * CMvPolynomial.X 3)),
        (((2644851949 / 140692275) : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (5 : ℚ) * CMvPolynomial.X 0) * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 3)),
        (((37463 / 200) : ℚ), CMvPolynomial.X 0 * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 1 + CMvPolynomial.C ((8159 / 37463) : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((-6770 / 37463) : ℚ) * CMvPolynomial.X 3)),
        (((17986011 / 74926) : ℚ), CMvPolynomial.X 0 * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((5235096 / 29976685) : ℚ) * CMvPolynomial.X 3)),
        (((534914011 / 5995337) : ℚ), CMvPolynomial.X 0 * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 3))] }),
    ([1], { terms := [
        (((15 / 2) : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (5 : ℚ) * CMvPolynomial.X 0) * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 1 + CMvPolynomial.C ((-1 / 300) : ℚ) * CMvPolynomial.X 2)),
        (((90599 / 12000) : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (5 : ℚ) * CMvPolynomial.X 0) * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((1800 / 90599) : ℚ) * CMvPolynomial.X 3)),
        (((724522 / 90599) : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (5 : ℚ) * CMvPolynomial.X 0) * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 3)),
        (((11273 / 20) : ℚ), CMvPolynomial.X 0 * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 1 + CMvPolynomial.C ((3347 / 22546) : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((-1388 / 11273) : ℚ) * CMvPolynomial.X 3)),
        (((610345719 / 901840) : ℚ), CMvPolynomial.X 0 * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((77515468 / 610345719) : ℚ) * CMvPolynomial.X 3)),
        (((1116746068612 / 3051728595) : ℚ), CMvPolynomial.X 0 * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 3))] })] }
noncomputable def energy (x v a : ℝ) : ℝ := ((38 / 5)) * x ^ 2 + ((514 / 25)) * x * v + (10) * x * a + ((1319 / 50)) * v ^ 2 + ((769 / 25)) * v * a + ((278 / 25)) * a ^ 2
noncomputable def nextX (h x v a : ℝ) : ℝ := ((1 / 8) * h ^ 2 + 1) * x + ((3 / 8) * h ^ 2 + 1 * h) * v + ((5 / 4) * h ^ 2) * a
noncomputable def nextV (h x v a : ℝ) : ℝ := ((-1 / 4) * h ^ 2) * x + ((-3 / 4) * h ^ 2 + 1) * v + ((-3 / 2) * h ^ 2 + 1 * h) * a
noncomputable def nextA (h x v a : ℝ) : ℝ := ((1 / 4) * h ^ 2 + (-1 / 4) * h) * x + ((3 / 4) * h ^ 2 + (-3 / 4) * h) * v + ((3 / 2) * h ^ 2 + (-3 / 2) * h + 1) * a
theorem residual_identity (h x v a : ℝ) :
    energy x v a - energy (nextX h x v a) (nextV h x v a) (nextA h x v a) -
      h * (x^2 + v^2 + a^2) = h * residual h x v a := by
  unfold energy nextX nextV nextA residual
  ring
theorem interval_decrease (h x v a : ℝ) (hlo : 0 ≤ h) (hhi : h ≤ (1 / 5)) :
    energy (nextX h x v a) (nextV h x v a) (nextA h x v a) ≤ energy x v a - h * (x^2+v^2+a^2) := by
  have hp := mul_nonneg hlo (residual_nonnegative h x v a hlo hhi)
  have hi := residual_identity h x v a
  linarith
#print axioms TravelSOSComparison.TravelQuarterUpper.residual_nonnegative
#print axioms TravelSOSComparison.TravelQuarterUpper.residual_identity
#print axioms TravelSOSComparison.TravelQuarterUpper.interval_decrease
end TravelQuarterUpper
namespace TravelFullLower
noncomputable def residual (h x v a : ℝ) : ℝ :=
    ((-19 / 10) * h ^ 3 + -5 * h ^ 2 + (-88 / 25) * h + 9) * x ^ 2 +
    ((-57 / 5) * h ^ 3 + (-112 / 5) * h ^ 2 + (-591 / 25) * h + (1139 / 25)) * x * v +
    ((-38 / 5) * h ^ 3 + (-368 / 25) * h ^ 2 + (-394 / 25) * h + (792 / 25)) * x * a +
    ((-171 / 10) * h ^ 3 + (-111 / 5) * h ^ 2 + (-1171 / 25) * h + (1768 / 25)) * v ^ 2 +
    ((-114 / 5) * h ^ 3 + (-724 / 25) * h ^ 2 + (-1572 / 25) * h + (2406 / 25)) * v * a +
    ((-38 / 5) * h ^ 3 + (-236 / 25) * h ^ 2 + (-1209 / 50) * h + (874 / 25)) * a ^ 2
theorem residual_nonnegative (h x v a : ℝ) (hlo : 0 ≤ h) (hhi : h ≤ (1 / 5)) :
    0 ≤ residual h x v a := by
  unfold residual
  sos_witness { sigmas := [
    ([0], { terms := [
        (((3287 / 25) : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (5 : ℚ) * CMvPolynomial.X 0) * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 1 + CMvPolynomial.C ((8247 / 3287) : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((5743 / 3287) : ℚ) * CMvPolynomial.X 3)),
        (((15309154 / 82175) : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (5 : ℚ) * CMvPolynomial.X 0) * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((4683906 / 7654577) : ℚ) * CMvPolynomial.X 3)),
        (((11137347877 / 382728850) : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (5 : ℚ) * CMvPolynomial.X 0) * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 3)),
        (((10101 / 10) : ℚ), CMvPolynomial.X 0 * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 1 + CMvPolynomial.C ((8301 / 3367) : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((5808 / 3367) : ℚ) * CMvPolynomial.X 3)),
        (((4718230 / 3367) : ℚ), CMvPolynomial.X 0 * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((1430113 / 2359115) : ℚ) * CMvPolynomial.X 3)),
        (((179418157 / 943646) : ℚ), CMvPolynomial.X 0 * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 3))] }),
    ([1], { terms := [
        ((45 : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (5 : ℚ) * CMvPolynomial.X 0) * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 1 + CMvPolynomial.C ((1139 / 450) : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((44 / 25) : ℚ) * CMvPolynomial.X 3)),
        (((293879 / 4500) : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (5 : ℚ) * CMvPolynomial.X 0) * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((180612 / 293879) : ℚ) * CMvPolynomial.X 3)),
        (((15783122 / 1469395) : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (5 : ℚ) * CMvPolynomial.X 0) * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 3)),
        ((3174 : ℚ), CMvPolynomial.X 0 * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 1 + CMvPolynomial.C ((15791 / 6348) : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((4591 / 2645) : ℚ) * CMvPolynomial.X 3)),
        (((56198951 / 12696) : ℚ), CMvPolynomial.X 0 * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((171152316 / 280994755) : ℚ) * CMvPolynomial.X 3)),
        (((36479407975 / 56198951) : ℚ), CMvPolynomial.X 0 * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 3))] })] }
noncomputable def energy (x v a : ℝ) : ℝ := ((38 / 5)) * x ^ 2 + ((514 / 25)) * x * v + (10) * x * a + ((1319 / 50)) * v ^ 2 + ((769 / 25)) * v * a + ((278 / 25)) * a ^ 2
noncomputable def nextX (h x v a : ℝ) : ℝ := ((-1 / 2) * h ^ 2 + 1) * x + ((-3 / 2) * h ^ 2 + 1 * h) * v + (-1 * h ^ 2) * a
noncomputable def nextV (h x v a : ℝ) : ℝ := (0) * x + (1) * v + (1 * h) * a
noncomputable def nextA (h x v a : ℝ) : ℝ := (-1 * h) * x + (-3 * h) * v + (-3 * h + 1) * a
theorem residual_identity (h x v a : ℝ) :
    energy x v a - energy (nextX h x v a) (nextV h x v a) (nextA h x v a) -
      h * (x^2 + v^2 + a^2) = h * residual h x v a := by
  unfold energy nextX nextV nextA residual
  ring
theorem interval_decrease (h x v a : ℝ) (hlo : 0 ≤ h) (hhi : h ≤ (1 / 5)) :
    energy (nextX h x v a) (nextV h x v a) (nextA h x v a) ≤ energy x v a - h * (x^2+v^2+a^2) := by
  have hp := mul_nonneg hlo (residual_nonnegative h x v a hlo hhi)
  have hi := residual_identity h x v a
  linarith
#print axioms TravelSOSComparison.TravelFullLower.residual_nonnegative
#print axioms TravelSOSComparison.TravelFullLower.residual_identity
#print axioms TravelSOSComparison.TravelFullLower.interval_decrease
end TravelFullLower
namespace TravelFullUpper
noncomputable def residual (h x v a : ℝ) : ℝ :=
    ((-84 / 25) * h ^ 3 + (-88 / 25) * h ^ 2 + (-204 / 25) * h + 9) * x ^ 2 +
    ((-504 / 25) * h ^ 3 + (-454 / 25) * h ^ 2 + (-903 / 25) * h + (1139 / 25)) * x * v +
    ((-467 / 25) * h ^ 3 + (-22 / 5) * h ^ 2 + (-779 / 25) * h + (792 / 25)) * x * a +
    ((-756 / 25) * h ^ 3 + (-114 / 5) * h ^ 2 + (-1063 / 25) * h + (1768 / 25)) * v ^ 2 +
    ((-1401 / 25) * h ^ 3 + (-298 / 25) * h ^ 2 + -63 * h + (2406 / 25)) * v * a +
    ((-277 / 10) * h ^ 3 + (41 / 5) * h ^ 2 + (-1431 / 50) * h + (874 / 25)) * a ^ 2
theorem residual_nonnegative (h x v a : ℝ) (hlo : 0 ≤ h) (hhi : h ≤ (1 / 5)) :
    0 ≤ residual h x v a := by
  unfold residual
  sos_witness { sigmas := [
    ([0], { terms := [
        (((3171 / 25) : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (5 : ℚ) * CMvPolynomial.X 0) * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 1 + CMvPolynomial.C ((2697 / 1057) : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((11101 / 6342) : ℚ) * CMvPolynomial.X 3)),
        (((5086622 / 26425) : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (5 : ℚ) * CMvPolynomial.X 0) * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((3271479 / 5086622) : ℚ) * CMvPolynomial.X 3)),
        (((21007885973 / 762993300) : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (5 : ℚ) * CMvPolynomial.X 0) * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 3)),
        (((22501 / 25) : ℚ), CMvPolynomial.X 0 * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 1 + CMvPolynomial.C ((58513 / 22501) : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((39254 / 22501) : ℚ) * CMvPolynomial.X 3)),
        (((34793886 / 22501) : ℚ), CMvPolynomial.X 0 * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((20373498 / 28994905) : ℚ) * CMvPolynomial.X 3)),
        (((957533863 / 5798981) : ℚ), CMvPolynomial.X 0 * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 3))] }),
    ([1], { terms := [
        ((45 : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (5 : ℚ) * CMvPolynomial.X 0) * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 1 + CMvPolynomial.C ((1139 / 450) : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((44 / 25) : ℚ) * CMvPolynomial.X 3)),
        (((293879 / 4500) : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (5 : ℚ) * CMvPolynomial.X 0) * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((180612 / 293879) : ℚ) * CMvPolynomial.X 3)),
        (((15783122 / 1469395) : ℚ), (CMvPolynomial.C (1 : ℚ) - CMvPolynomial.C (5 : ℚ) * CMvPolynomial.X 0) * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 3)),
        (((14747 / 5) : ℚ), CMvPolynomial.X 0 * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 1 + CMvPolynomial.C ((75941 / 29494) : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((25750 / 14747) : ℚ) * CMvPolynomial.X 3)),
        (((1394107719 / 294940) : ℚ), CMvPolynomial.X 0 * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 2 + CMvPolynomial.C ((937911088 / 1394107719) : ℚ) * CMvPolynomial.X 3)),
        (((4099279250212 / 6970538595) : ℚ), CMvPolynomial.X 0 * (CMvPolynomial.C (1 : ℚ) * CMvPolynomial.X 3))] })] }
noncomputable def energy (x v a : ℝ) : ℝ := ((38 / 5)) * x ^ 2 + ((514 / 25)) * x * v + (10) * x * a + ((1319 / 50)) * v ^ 2 + ((769 / 25)) * v * a + ((278 / 25)) * a ^ 2
noncomputable def nextX (h x v a : ℝ) : ℝ := ((1 / 2) * h ^ 2 + 1) * x + ((3 / 2) * h ^ 2 + 1 * h) * v + (2 * h ^ 2) * a
noncomputable def nextV (h x v a : ℝ) : ℝ := (-1 * h ^ 2) * x + (-3 * h ^ 2 + 1) * v + (-3 * h ^ 2 + 1 * h) * a
noncomputable def nextA (h x v a : ℝ) : ℝ := (1 * h ^ 2 + -1 * h) * x + (3 * h ^ 2 + -3 * h) * v + (3 * h ^ 2 + -3 * h + 1) * a
theorem residual_identity (h x v a : ℝ) :
    energy x v a - energy (nextX h x v a) (nextV h x v a) (nextA h x v a) -
      h * (x^2 + v^2 + a^2) = h * residual h x v a := by
  unfold energy nextX nextV nextA residual
  ring
theorem interval_decrease (h x v a : ℝ) (hlo : 0 ≤ h) (hhi : h ≤ (1 / 5)) :
    energy (nextX h x v a) (nextV h x v a) (nextA h x v a) ≤ energy x v a - h * (x^2+v^2+a^2) := by
  have hp := mul_nonneg hlo (residual_nonnegative h x v a hlo hhi)
  have hi := residual_identity h x v a
  linarith
#print axioms TravelSOSComparison.TravelFullUpper.residual_nonnegative
#print axioms TravelSOSComparison.TravelFullUpper.residual_identity
#print axioms TravelSOSComparison.TravelFullUpper.interval_decrease
end TravelFullUpper
end TravelSOSComparison

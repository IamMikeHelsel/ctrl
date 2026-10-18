module
public import LeanControls.UncertainLag
@[expose] public section
noncomputable section
namespace LeanControls.IntervalChecker
open UncertainLag (State)

/-- Exact rational endpoints. Empty intervals are allowed but contain no real. -/
structure Interval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq

def Mem (I : Interval) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)
def point (q : ℚ) : Interval := ⟨q,q⟩
def add (I J : Interval) : Interval := ⟨I.lo+J.lo,I.hi+J.hi⟩
def neg (I : Interval) : Interval := ⟨-I.hi,-I.lo⟩
def sub (I J : Interval) : Interval := add I (neg J)
def mul (I J : Interval) : Interval :=
  ⟨min (min (I.lo*J.lo) (I.hi*J.lo)) (min (I.lo*J.hi) (I.hi*J.hi)),
   max (max (I.lo*J.lo) (I.hi*J.lo)) (max (I.lo*J.hi) (I.hi*J.hi))⟩
def clip1 (I : Interval) : Interval :=
  ⟨max (-1) (min 1 I.lo), max (-1) (min 1 I.hi)⟩

theorem point_mem (q : ℚ) : Mem (point q) (q : ℝ) := ⟨le_rfl,le_rfl⟩
theorem add_mem {I J : Interval} {x y : ℝ} (hx : Mem I x) (hy : Mem J y) :
    Mem (add I J) (x+y) := by
  simpa [Mem,add] using And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)
theorem neg_mem {I : Interval} {x : ℝ} (hx : Mem I x) : Mem (neg I) (-x) := by
  simpa [Mem,neg] using And.intro (neg_le_neg hx.2) (neg_le_neg hx.1)
theorem sub_mem {I J : Interval} {x y : ℝ} (hx : Mem I x) (hy : Mem J y) :
    Mem (sub I J) (x-y) := by simpa [sub,sub_eq_add_neg] using add_mem hx (neg_mem hy)

private theorem scale_bounds {a b x : ℝ} (hx : a ≤ x ∧ x ≤ b) (c : ℝ) :
    min (a*c) (b*c) ≤ x*c ∧ x*c ≤ max (a*c) (b*c) := by
  by_cases hc : 0 ≤ c
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx.1 hc),
      (mul_le_mul_of_nonneg_right hx.2 hc).trans (le_max_right _ _)⟩
  · have hc' : c ≤ 0 := le_of_not_ge hc
    exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx.2 hc'),
      (mul_le_mul_of_nonpos_right hx.1 hc').trans (le_max_left _ _)⟩

theorem mul_mem {I J : Interval} {x y : ℝ} (hx : Mem I x) (hy : Mem J y) :
    Mem (mul I J) (x*y) := by
  have hlo := scale_bounds hx (J.lo : ℝ)
  have hhi := scale_bounds hx (J.hi : ℝ)
  have hxy : min (x*(J.lo:ℝ)) (x*(J.hi:ℝ)) ≤ x*y ∧
      x*y ≤ max (x*(J.lo:ℝ)) (x*(J.hi:ℝ)) := by
    simpa only [mul_comm] using scale_bounds hy x
  have hl := (min_le_min hlo.1 hhi.1).trans hxy.1
  have hu := hxy.2.trans (max_le_max hlo.2 hhi.2)
  simpa [Mem,mul,mul_comm] using And.intro hl hu

theorem clip1_mem {I : Interval} {x : ℝ} (hx : Mem I x) :
    Mem (clip1 I) (RobustPD.saturate 1 x) := by
  have hlo : max (-1:ℝ) (min 1 (I.lo:ℝ)) ≤ max (-1) (min 1 x) :=
    max_le_max le_rfl (min_le_min le_rfl hx.1)
  have hhi : max (-1:ℝ) (min 1 x) ≤ max (-1) (min 1 (I.hi:ℝ)) :=
    max_le_max le_rfl (min_le_min le_rfl hx.2)
  simpa [Mem,clip1,RobustPD.saturate] using And.intro hlo hhi

abbrev Box := Fin 3 → Interval
def BoxMem (X : Box) (z : State) : Prop := ∀ i, Mem (X i) (z i)

/-- Rational bounds for the exact coefficients. No exponential approximation
is trusted here; callers must prove each real membership. -/
structure Coefficients where
  dt : Interval
  halfSq : Interval
  E : Interval
  B : Interval
  C : Interval

def CoeffMem (K : Coefficients) (r h : ℝ) : Prop :=
  Mem K.dt h ∧ Mem K.halfSq (h^2/2) ∧ Mem K.E (Real.exp (-r*h)) ∧
  Mem K.B ((1-Real.exp (-r*h))/r) ∧ Mem K.C (h/r-(1-Real.exp (-r*h))/r^2)

def heldBox (K : Coefficients) (X : Box) (U : Interval) : Box :=
  ![add (add (add (X 0) (mul K.dt (X 1))) (mul K.C (X 2)))
      (mul (sub K.halfSq K.C) U),
    add (add (X 1) (mul K.B (X 2))) (mul (sub K.dt K.B) U),
    add (mul K.E (X 2)) (mul (sub (point 1) K.E) U)]

/-- Exact analytic held-flow containment. Factoring by independent state and
command coordinates reduces interval wrapping; soundness is an exact identity. -/
theorem heldBox_sound {K : Coefficients} {r h u : ℝ} {X : Box} {U : Interval}
    {z : State} (hk : CoeffMem K r h) (hz : BoxMem X z) (hu : Mem U u) :
    BoxMem (heldBox K X U) (UncertainLag.heldSolution r h u z) := by
  rcases hk with ⟨hh,hh2,he,hb,hc⟩
  intro i
  fin_cases i
  · have hx := add_mem (add_mem (add_mem (hz 0) (mul_mem hh (hz 1)))
      (mul_mem hc (hz 2))) (mul_mem (sub_mem hh2 hc) hu)
    convert hx using 1 <;> simp [heldBox,UncertainLag.heldSolution] <;> ring
  · have hv := add_mem (add_mem (hz 1) (mul_mem hb (hz 2))) (mul_mem (sub_mem hh hb) hu)
    convert hv using 1 <;> simp [heldBox,UncertainLag.heldSolution] <;> ring
  · have ha := add_mem (mul_mem he (hz 2)) (mul_mem (sub_mem (point_mem 1) he) hu)
    convert ha using 1 <;> simp [heldBox,UncertainLag.heldSolution] <;> ring

/-- Enclose the actual sampled request, pre-clamp error, and post-clamp error. -/
def commandBox (X : Box) (e d : Interval) : Interval :=
  add (clip1 (add (neg (add (add (X 0) (mul (point 3) (X 1)))
    (mul (point 2) (X 2)))) e)) d

theorem commandBox_sound {X : Box} {ei di : Interval} {z : State} {e d : ℝ}
    (hz : BoxMem X z) (he : Mem ei e) (hd : Mem di d) :
    Mem (commandBox X ei di) (RobustPD.saturate 1 (UncertainLag.input z+e)+d) := by
  have h := add_mem (clip1_mem (add_mem (neg_mem (add_mem
    (add_mem (hz 0) (mul_mem (point_mem 3) (hz 1)))
    (mul_mem (point_mem 2) (hz 2)))) he)) hd
  convert h using 1 <;> simp [commandBox,UncertainLag.input,SaturatedLag.input] <;> ring

def sampledBox (K : Coefficients) (X : Box) (e d : Interval) : Box :=
  heldBox K X (commandBox X e d)

theorem sampledBox_sound {K : Coefficients} {r h : ℝ} {X : Box} {ei di : Interval}
    {z : State} {e d : ℝ} (hk : CoeffMem K r h) (hz : BoxMem X z)
    (he : Mem ei e) (hd : Mem di d) :
    BoxMem (sampledBox K X ei di)
      (UncertainLag.heldSolution r h (RobustPD.saturate 1 (UncertainLag.input z+e)+d) z) :=
  heldBox_sound hk hz (commandBox_sound hz he hd)

/-- State and interval trace use each step's own sampled state. Rates and
errors may vary by step, but each step uses one held rate and held command. -/
def stateTrace (r h e d : ℕ → ℝ) (z0 : State) : ℕ → State
  | 0 => z0
  | n+1 => UncertainLag.heldSolution (r n) (h n)
      (RobustPD.saturate 1 (UncertainLag.input (stateTrace r h e d z0 n)+e n)+d n)
      (stateTrace r h e d z0 n)

def boxTrace (K : ℕ → Coefficients) (ei di : ℕ → Interval) (X0 : Box) : ℕ → Box
  | 0 => X0
  | n+1 => sampledBox (K n) (boxTrace K ei di X0 n) (ei n) (di n)

/-- Composition is finite and only needs coefficient/error bounds for n<N.
This is endpoint containment, not an unstated continuous-path safety claim. -/
theorem trace_sound {N : ℕ} (r h e d : ℕ → ℝ) (K : ℕ → Coefficients)
    (ei di : ℕ → Interval) {z0 : State} {X0 : Box}
    (h0 : BoxMem X0 z0) (hk : ∀ n<N, CoeffMem (K n) (r n) (h n))
    (he : ∀ n<N, Mem (ei n) (e n)) (hd : ∀ n<N, Mem (di n) (d n)) :
    ∀ n≤N, BoxMem (boxTrace K ei di X0 n) (stateTrace r h e d z0 n) := by
  intro n hn
  induction n with
  | zero => exact h0
  | succ n ih =>
      exact sampledBox_sound (hk n (by omega)) (ih (by omega))
        (he n (by omega)) (hd n (by omega))

/-- Checkable rational endpoint inclusion, permitting outward rounding after
any step. This avoids repeatedly carrying growing exact rational expressions. -/
def Subset (I J : Interval) : Prop := J.lo ≤ I.lo ∧ I.hi ≤ J.hi
instance (I J : Interval) : Decidable (Subset I J) := inferInstanceAs (Decidable (_ ∧ _))
def BoxSubset (X Y : Box) : Prop := ∀ i, Subset (X i) (Y i)
instance (X Y : Box) : Decidable (BoxSubset X Y) := inferInstanceAs (Decidable (∀ i, _))

theorem subset_mem {I J : Interval} {x : ℝ} (h : Subset I J) (hx : Mem I x) : Mem J x := by
  have hlo : (J.lo:ℝ) ≤ (I.lo:ℝ) := by exact_mod_cast h.1
  have hhi : (I.hi:ℝ) ≤ (J.hi:ℝ) := by exact_mod_cast h.2
  exact ⟨hlo.trans hx.1, hx.2.trans hhi⟩

/-- A finite certificate supplies boxes and checks each outward-rounded step.
The conclusion concerns the real own-sample-feedback recurrence, not a trace
assumed equal to a chosen numerical candidate. -/
theorem certificate_trace_sound {N : ℕ} (r h e d : ℕ → ℝ) (K : ℕ → Coefficients)
    (ei di : ℕ → Interval) (X : ℕ → Box) {z0 : State}
    (h0 : BoxMem (X 0) z0) (hk : ∀ n<N, CoeffMem (K n) (r n) (h n))
    (he : ∀ n<N, Mem (ei n) (e n)) (hd : ∀ n<N, Mem (di n) (d n))
    (hstep : ∀ n<N, BoxSubset (sampledBox (K n) (X n) (ei n) (di n)) (X (n+1))) :
    ∀ n≤N, BoxMem (X n) (stateTrace r h e d z0 n) := by
  intro n hn
  induction n with
  | zero => exact h0
  | succ n ih =>
      have hs := sampledBox_sound (hk n (by omega)) (ih (by omega))
        (he n (by omega)) (hd n (by omega))
      exact fun i => subset_mem (hstep n (by omega) i) (hs i)

end LeanControls.IntervalChecker
#print axioms LeanControls.IntervalChecker.mul_mem
#print axioms LeanControls.IntervalChecker.heldBox_sound
#print axioms LeanControls.IntervalChecker.commandBox_sound
#print axioms LeanControls.IntervalChecker.sampledBox_sound
#print axioms LeanControls.IntervalChecker.trace_sound

#print axioms LeanControls.IntervalChecker.subset_mem
#print axioms LeanControls.IntervalChecker.certificate_trace_sound

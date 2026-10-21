import Mathlib.Tactic
noncomputable section
namespace R07
def lower (v l₁ h₂ : ℝ) : ℝ := max (l₁-v/2) (v/2-h₂)
def upper (v h₁ l₂ : ℝ) : ℝ := min (h₁-v/2) (v/2-l₂)
def clip (lo hi n : ℝ) : ℝ := if n<lo then lo else if hi<n then hi else n

theorem allocation_interval (v n l₁ h₁ l₂ h₂ : ℝ) :
    (l₁≤v/2+n ∧ v/2+n≤h₁ ∧ l₂≤v/2-n ∧ v/2-n≤h₂) ↔
    (lower v l₁ h₂≤n ∧ n≤upper v h₁ l₂) := by
  simp only [lower,upper,max_le_iff,le_min_iff]
  constructor
  · rintro ⟨h1,h2,h3,h4⟩
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩
  · rintro ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem task_rate (v n : ℝ) : (v/2+n)+(v/2-n)=v := by ring

theorem all_allocations (v u₁ u₂ : ℝ) (h : u₁+u₂=v) :
    u₁=v/2+(u₁-u₂)/2 ∧ u₂=v/2-(u₁-u₂)/2 := by constructor <;> linarith

theorem clip_feasible (lo hi n : ℝ) (h : lo≤hi) :
    lo≤clip lo hi n ∧ clip lo hi n≤hi := by
  unfold clip
  split_ifs <;> constructor <;> linarith

theorem no_intervention_iff (lo hi n : ℝ) (h : lo≤hi) :
    clip lo hi n=n ↔ lo≤n ∧ n≤hi := by
  constructor
  · intro he
    simpa only [he] using clip_feasible lo hi n h
  · rintro ⟨hl,hh⟩
    simp [clip,not_lt.mpr hl,not_lt.mpr hh]

theorem least_intervention (lo hi n m : ℝ) (hl : lo≤m) (hh : m≤hi) :
    (clip lo hi n-n)^2≤(m-n)^2 := by
  unfold clip
  split_ifs with hn hn
  · nlinarith [mul_nonneg (sub_nonneg.mpr hl) (show 0≤m+lo-2*n by linarith)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hh) (show 0≤2*n-m-hi by linarith)]
  · nlinarith [sq_nonneg (m-n)]

theorem actual_cost (v n n₀ : ℝ) :
    ((v/2+n)-(v/2+n₀))^2+((v/2-n)-(v/2-n₀))^2=2*(n-n₀)^2 := by ring

/-- Exact finite-horizon ZOH certificate; both endpoint constraints are required. -/
theorem affine_segment_safe (a d b T t : ℝ) (hT : 0<T)
    (ht0 : 0≤t) (htT : t≤T) (h0 : a≤b) (h1 : a+T*d≤b) :
    a+t*d≤b := by
  have hn := add_nonneg
    (mul_nonneg (sub_nonneg.mpr htT) (sub_nonneg.mpr h0))
    (mul_nonneg ht0 (sub_nonneg.mpr h1))
  nlinarith

theorem halfspace_alltime (q₁ q₂ u₁ u₂ a₁ a₂ b T t : ℝ) (hT : 0<T)
    (ht0 : 0≤t) (htT : t≤T)
    (h0 : a₁*q₁+a₂*q₂≤b)
    (h1 : a₁*(q₁+T*u₁)+a₂*(q₂+T*u₂)≤b) :
    a₁*(q₁+t*u₁)+a₂*(q₂+t*u₂)≤b := by
  have hh := affine_segment_safe (a₁*q₁+a₂*q₂) (a₁*u₁+a₂*u₂) b T t hT ht0 htT h0
    (by nlinarith [h1])
  nlinarith [hh]

theorem null_motion_can_hit_obstacle :
    (2/5:ℝ)+(3/5)=1 ∧ ((2/5:ℝ)+(1/5))+((3/5)-(1/5))=1 ∧
    (2/5:ℝ)≤3/5 ∧ ¬((2/5:ℝ)+(1/5)≤(3/5)-(1/5)) := by norm_num
/-- The selected boundary velocity retains the task and all declared geometric
and input constraints throughout the entire one-second hold. -/
theorem fixture_alltime (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) :
    let q₁ := 2/5+t/10
    let q₂ := 3/5-t/10
    q₁+q₂=1 ∧ 0≤q₁ ∧ q₁≤1 ∧ 0≤q₂ ∧ q₂≤1 ∧ q₁≤q₂ ∧
    |(1/10:ℝ)|≤1/4 ∧ |(-1/10:ℝ)|≤1/4 := by
  dsimp
  exact ⟨by ring,by linarith,by linarith,by linarith,by linarith,by linarith,by norm_num,by norm_num⟩

#print axioms fixture_alltime
#print axioms allocation_interval
#print axioms task_rate
#print axioms all_allocations
#print axioms clip_feasible
#print axioms no_intervention_iff
#print axioms least_intervention
#print axioms actual_cost
#print axioms affine_segment_safe
#print axioms halfspace_alltime
#print axioms null_motion_can_hit_obstacle
end R07

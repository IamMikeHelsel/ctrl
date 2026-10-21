module
public import AgeBudget
public import Mathlib.Algebra.Order.Floor.Semiring
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LeanControls.TimingClock
open Set DigitalHold

def period : ℝ := 1/1000
def delay : ℝ := 1/2000
def sample (n : ℕ) : ℝ := n/1000
def dispatch (n : ℕ) : ℝ := delay+sample n
def index (b : Bool) (t : ℝ) : ℕ :=
  if b then Nat.floor (1000*(t-delay)) else Nat.ceil (1000*(t-delay))-1
def stamp (b : Bool) (t : ℝ) : ℝ := sample (index b t)+delay
def schedule (m : ℕ→State) : Schedule where
  sample := sample
  dispatch := dispatch
  measurement := m
  index := index

theorem startup_index (b : Bool) {t : ℝ} (ht : t≤delay) : index b t=0 := by
  have h0 : (1000:ℝ)*(t-delay)≤0 := by linarith
  cases b
  · simp [index,Nat.ceil_eq_zero.mpr h0]
  · simp [index,Nat.floor_eq_zero.mpr (show (1000:ℝ)*(t-delay)<1 by linarith)]

theorem right_cell {t : ℝ} (ht : delay≤t) :
    dispatch (index true t)≤t ∧ t<dispatch (index true t+1) := by
  have hlo := Nat.floor_le (show 0≤(1000:ℝ)*(t-delay) by linarith)
  have hhi := Nat.lt_floor_add_one ((1000:ℝ)*(t-delay))
  norm_num [dispatch,sample,index,Nat.cast_add] at *
  constructor <;> linarith

theorem left_cell {t : ℝ} (ht : delay<t) :
    dispatch (index false t)<t ∧ t≤dispatch (index false t+1) := by
  have hpos : 1≤Nat.ceil ((1000:ℝ)*(t-delay)) := Nat.one_le_ceil_iff.mpr (by linarith)
  have hn : Nat.ceil ((1000:ℝ)*(t-delay))≠0 := by omega
  have hh := (Nat.ceil_eq_iff hn).mp (rfl : Nat.ceil ((1000:ℝ)*(t-delay))=Nat.ceil ((1000:ℝ)*(t-delay)))
  have he : Nat.ceil ((1000:ℝ)*(t-delay))-1+1=Nat.ceil ((1000:ℝ)*(t-delay)) := Nat.sub_add_cancel hpos
  have her : ((Nat.ceil ((1000:ℝ)*(t-delay))-1:ℕ):ℝ)+1=(Nat.ceil ((1000:ℝ)*(t-delay)):ℝ) := by
    exact_mod_cast he
  norm_num [dispatch,sample,index] at *
  rw [her]
  constructor <;> linarith

theorem sample_dispatch (n : ℕ) : 0≤sample n ∧ sample n≤dispatch n := by
  dsimp [sample,dispatch,delay]
  exact ⟨by positivity,by linarith⟩

theorem dispatch_strict : StrictMono dispatch := by
  intro m n hmn
  have hh : (m:ℝ)<n := by exact_mod_cast hmn
  dsimp [dispatch,sample]; linarith

theorem dispatch_locally_finite (T : ℝ) : Set.Finite {n | dispatch n≤T} := by
  obtain ⟨N,hN⟩ := exists_nat_gt (1000*T)
  apply Set.Finite.subset (Set.finite_Iio N)
  intro n hn
  change n<N
  have hh : (n:ℝ)<N := by dsimp [dispatch,sample,delay] at hn; linarith
  exact_mod_cast hh

theorem stamp_age {t : ℝ} (ht : 0≤t) (b : Bool) :
    0≤stamp b t ∧ stamp b t≤t ∧ t-stamp b t≤TimingBudget.age := by
  have hnonneg : 0≤stamp b t := by dsimp [stamp,sample]; positivity
  refine ⟨hnonneg,?_⟩
  by_cases hpre : t≤delay
  · rw [stamp,startup_index b hpre]
    norm_num [sample,TimingBudget.age]
    norm_num [delay] at hpre
    exact ⟨ht,by linarith⟩
  · cases b
    · have hh := left_cell (lt_of_not_ge hpre)
      norm_num [dispatch,sample,Nat.cast_add,delay] at hh
      dsimp [stamp,sample,TimingBudget.age]
      constructor <;> linarith
    · have hh := right_cell (le_of_not_ge hpre)
      norm_num [dispatch,sample,Nat.cast_add,delay] at hh
      dsimp [stamp,sample,TimingBudget.age]
      constructor <;> linarith

theorem sample_and_delay_separate :
    sample 1-sample 0=1/1000 ∧ dispatch 0=1/2000 ∧
    dispatch 1=3/2000 ∧ TimingBudget.age=period+delay := by
  norm_num [sample,dispatch,period,delay,TimingBudget.age]

/-- The incoming command still uses sample zero at the second dispatch. -/
theorem second_dispatch_sides :
    stamp false (dispatch 1)=0 ∧ stamp true (dispatch 1)=1/1000 ∧
    dispatch 1-stamp false (dispatch 1)=3/2000 ∧
    dispatch 1-stamp true (dispatch 1)=1/2000 := by
  norm_num [stamp,index,dispatch,sample,delay]

theorem old_age_cap_false : ¬dispatch 1-stamp false (dispatch 1)≤1/1000 := by
  rw [second_dispatch_sides.2.2.1]
  norm_num

end LeanControls.TimingClock

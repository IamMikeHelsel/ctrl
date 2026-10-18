import CutWitness
import ScalarCertificate
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
namespace Erdos128.CompletionBridge

/-- Exact normalized algebra connecting the two graph cut witnesses to the
pinned scalar certificate. q,j are actual normalized internal edge counts
when this lemma is instantiated in the graph wrapper. -/
theorem cut_scalar_bound (c x q j beta : ℚ)
    (hc : 0 < c) (hcx : 2 * c * (1 - x) = 1)
    (hq : 0 ≤ q) (hcut : q + j ≤ SparseHalf.I)
    (hfirst : beta ≤ c ^ 2 * j)
    (hsecond : SparseHalf.c0 ≤ c → beta ≤ completionEnvelope x (1 / 2) + q) :
    beta < SparseHalf.T := by
  have hcn : c ≠ 0 := ne_of_gt hc
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  have hj : j ≤ SparseHalf.I := by linarith
  have hcap : beta ≤ SparseHalf.I * c * c := by
    have hm := mul_le_mul_of_nonneg_left hj hc2
    nlinarith
  have hxpos : 0 < 1 - x := by
    by_contra h
    have hm := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 2 * c by linarith) (le_of_not_gt h)
    nlinarith
  have hx : x = 1 - 1 / (2 * c) := by
    field_simp [hcn]
    nlinarith [hcx]
  have hcombined (hl : SparseHalf.c0 ≤ c) :
      (1 + c * c) * beta ≤ c ^ 2 * (SparseHalf.I + completionEnvelope x (1 / 2)) := by
    have hs := mul_le_mul_of_nonneg_left (hsecond hl) hc2
    have htot := mul_le_mul_of_nonneg_left hcut hc2
    nlinarith
  apply SparseHalf.scalar_envelope c beta hc.le hcap
  · intro hl hu
    have hm := mul_le_mul_of_nonneg_right hu hxpos.le
    have hbranch : 4 * x ≤ 3 * (1 / 2 : ℚ) := by nlinarith [hcx]
    have hbound := hcombined hl
    rw [completionEnvelope, if_pos hbranch] at hbound
    have heq : c ^ 2 * (SparseHalf.I +
        (3 * x ^ 2 / 2 - 5 * x * (1 / 2) / 2 + 9 * (1 / 2 : ℚ) ^ 2 / 8)) =
        (SparseHalf.I + 17 / 32) * c * c - 7 * c / 8 + 3 / 8 := by
      rw [hx]
      field_simp [hcn]
      ring
    rwa [heq] at hbound
  · intro hl
    have hlow : SparseHalf.c0 ≤ c := by dsimp [SparseHalf.c0]; linarith
    have hm := mul_le_mul_of_nonneg_right hl hxpos.le
    have hbranch : 3 * (1 / 2 : ℚ) ≤ 4 * x := by nlinarith [hcx]
    have henv : completionEnvelope x (1 / 2) = x * (1 / 2 - x) / 2 := by
      unfold completionEnvelope
      split_ifs with h
      · have hxv : x = 3 / 8 := by linarith
        rw [hxv]
        norm_num
      · rfl
    have hbound := hcombined hlow
    rw [henv] at hbound
    have heq : c ^ 2 * (SparseHalf.I + x * (1 / 2 - x) / 2) =
        (SparseHalf.I - 1 / 4) * c * c + 3 * c / 8 - 1 / 8 := by
      rw [hx]
      field_simp [hcn]
      ring
    rwa [heq] at hbound

end Erdos128.CompletionBridge
#print axioms Erdos128.CompletionBridge.cut_scalar_bound

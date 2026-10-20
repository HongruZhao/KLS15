import Mathlib

/-! A sharp one-step constant-weight tail payment from the actual quadratic
observation cap.  This is a scalar lemma; it asserts no new KLS constant. -/
noncomputable section
namespace KLSConstantImprovement.QuadraticCapTailStep

def lowerExcess (A r : ℝ) : ℝ := max 0 (r-A/r-1)

theorem lowerExcess_nonneg (A r : ℝ) : 0 ≤ lowerExcess A r :=
  le_max_left _ _

/-- The true quadratic cap pays an extra square beyond the ordinary
constant-tail line.  The next ratio may rise or fall, and may be below one. -/
theorem one_step_payment {A τ r s d : ℝ}
    (hτ : 0 ≤ τ) (hr : 1 ≤ r) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (hdrop : r-s ≤ d) (hcap : d ≤ A/r) :
    τ*((r-1)+(lowerExcess A r)^2) ≤
      τ*d+s*max 0 (τ*(s-1)) := by
  have hlower : r-A/r ≤ s := by linarith
  by_cases hs1 : s ≤ 1
  · have he : lowerExcess A r=0 := by
      unfold lowerExcess
      exact max_eq_left (by linarith)
    have ht : max 0 (τ*(s-1))=0 := by
      exact max_eq_left (mul_nonpos_of_nonneg_of_nonpos hτ (by linarith))
    rw [he,ht]
    simp only [zero_pow,add_zero,mul_zero,add_zero]
    exact mul_le_mul_of_nonneg_left (by linarith) hτ
  · have hs1' : 1 ≤ s := (lt_of_not_ge hs1).le
    have he0 := lowerExcess_nonneg A r
    have he1 : lowerExcess A r ≤ s-1 := by
      exact max_le (by linarith) (by linarith)
    have he2 : (lowerExcess A r)^2 ≤ (s-1)^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr he1)
        (show 0 ≤ s-1+lowerExcess A r by linarith)]
    have ht : max 0 (τ*(s-1))=τ*(s-1) := by
      exact max_eq_right (mul_nonneg hτ (by linarith))
    have hpay : (r-1)+(lowerExcess A r)^2 ≤ d+s*(s-1) := by
      nlinarith
    have hp := mul_le_mul_of_nonneg_left hpay hτ
    rw [ht]
    nlinarith only [hp]

theorem lowerExcess_eq_zero_iff {A r : ℝ} (hr : 0 < r) :
    lowerExcess A r=0 ↔ r*(r-1) ≤ A := by
  unfold lowerExcess
  rw [max_eq_left_iff]
  constructor
  · intro h
    have hh : r-1 ≤ A/r := by linarith
    simpa only [mul_comm] using (le_div_iff₀ hr).mp hh
  · intro h
    have hh : r-1 ≤ A/r := (le_div_iff₀ hr).mpr (by simpa only [mul_comm] using h)
    linarith

end KLSConstantImprovement.QuadraticCapTailStep
#print axioms KLSConstantImprovement.QuadraticCapTailStep.one_step_payment
#print axioms KLSConstantImprovement.QuadraticCapTailStep.lowerExcess_eq_zero_iff

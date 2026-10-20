import Mathlib

/-! Exact retained-square algebra.  The mixed-pairing hypothesis below is a
research target at the actual joint maximizer, not a proved Appell estimate. -/
noncomputable section
namespace KLSBelow25
open InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem retained_square_identity (W V : H) (α : ℝ) :
    ‖W‖^2-2*⟪W,V⟫_ℝ+‖V‖^2/2 =
      α*‖W‖^2-(α+1/2)*‖V‖^2-2*α*⟪W-V,V⟫_ℝ+
        (1-α)*‖W-V‖^2 := by
  rw [norm_sub_sq_real, inner_sub_left, real_inner_self_eq_norm_sq]
  ring

theorem retained_square_lower_bound (W V : H) {α L : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hmixed : ⟪W-V,V⟫_ℝ ≤ L) :
    α*‖W‖^2-(α+1/2)*‖V‖^2-2*α*L ≤
      ‖W‖^2-2*⟪W,V⟫_ℝ+‖V‖^2/2 := by
  rw [retained_square_identity W V α]
  have hm := mul_le_mul_of_nonneg_left hmixed (show 0 ≤ 2*α by positivity)
  have hs := mul_nonneg (sub_nonneg.mpr hα1) (sq_nonneg ‖W-V‖)
  linarith

/-- The exponential two-slot scalar extremizer prevents a universal
pointwise improvement of the factor four used for the covariance tensor. -/
theorem sharp_scalar_two_slot_four {c : ℝ}
    (h : ∀ t : ℝ, (2*t)^2 ≤ c*t^2) : 4 ≤ c := by
  have := h 1
  norm_num at this
  exact this

#print axioms retained_square_identity
#print axioms retained_square_lower_bound
#print axioms sharp_scalar_two_slot_four
end KLSBelow25

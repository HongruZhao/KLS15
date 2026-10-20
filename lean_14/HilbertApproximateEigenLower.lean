import Mathlib

/-! The Hilbert-space lower estimate in the approximate spectral argument. -/
noncomputable section
open scoped InnerProductSpace
namespace KLSBelow25
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem adjoint_unit_residual_lower (T : H →L[ℂ] H) (z : ℂ)
    (v : H) (hunit : ‖v‖ = 1) :
    ‖z‖ ≤ ‖T.adjoint v‖ + ‖T v - z • v‖ := by
  have htriangle := norm_le_norm_add_norm_sub
    (inner ℂ v (T v)) (inner ℂ v (z • v))
  have hfirst := norm_inner_le_norm (𝕜 := ℂ) (T.adjoint v) v
  have hsecond := norm_inner_le_norm (𝕜 := ℂ) v (T v - z • v)
  rw [T.adjoint_inner_left] at hfirst
  rw [← inner_sub_right] at htriangle
  simpa [inner_smul_right, inner_self_eq_norm_sq_to_K, hunit] using
    htriangle.trans (add_le_add hfirst hsecond)

end KLSBelow25
#print axioms KLSBelow25.adjoint_unit_residual_lower

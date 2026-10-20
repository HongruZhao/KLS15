import Mathlib

/-! Hilbert-space identities for the projected same-response route.
The actual common-law Poisson identity, compatible Hessian projection,
response Riesz identification, and uniform combined-energy estimate remain
explicit inputs. No universal analytic estimate is asserted here. -/
noncomputable section
namespace KLSConstantImprovement.CompatibleHessianCombinedSquare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The part of the main field orthogonal to this same Hessian cancels
exactly against its matching negative square. -/
theorem same_hessian_projection_identity (s z p : E) {V response curvature : ℝ}
    (hidentity : V = ‖z‖ ^ 2 + 6 * response - ‖s-z‖ ^ 2 - curvature)
    (hcompatible : inner ℝ s (z-p) = 0) :
    V = ‖p‖ ^ 2 + 6 * response - ‖s-p‖ ^ 2 - curvature := by
  have hp : inner ℝ s z = inner ℝ s p := by
    rw [inner_sub_right] at hcompatible
    linarith
  rw [norm_sub_sq_real] at hidentity ⊢
  rw [hp] at hidentity
  linarith

/-- Keep the signed cross term between the compatible main and response. -/
theorem combined_square_identity (s p b : E) :
    ‖p‖ ^ 2 + 6 * inner ℝ b s - ‖s-p‖ ^ 2 =
      ‖p+(3 : ℝ) • b‖ ^ 2 - ‖s-(p+(3 : ℝ) • b)‖ ^ 2 := by
  simp only [norm_sub_sq_real, inner_add_right, inner_smul_right]
  rw [real_inner_comm b s]
  ring

theorem same_response_combined_identity (s z p b : E)
    {V response curvature : ℝ}
    (hidentity : V = ‖z‖ ^ 2 + 6 * response - ‖s-z‖ ^ 2 - curvature)
    (hcompatible : inner ℝ s (z-p) = 0)
    (hresponse : response = inner ℝ b s) :
    V = ‖p+(3 : ℝ) • b‖ ^ 2 - ‖s-(p+(3 : ℝ) • b)‖ ^ 2 - curvature := by
  have h := same_hessian_projection_identity s z p hidentity hcompatible
  rw [hresponse, combined_square_identity] at h
  exact h

/-- The combined projected-energy budget is sufficient for the open
integrated deficit gate; its uniform original-law proof is still missing. -/
theorem combined_energy_pays_additive_gate (s z p b : E)
    {V response curvature N signed : ℝ}
    (hidentity : V = ‖z‖ ^ 2 + 6 * response - ‖s-z‖ ^ 2 - curvature)
    (hcompatible : inner ℝ s (z-p) = 0)
    (hresponse : response = inner ℝ b s)
    (hbudget : ‖p+(3 : ℝ) • b‖ ^ 2 ≤ 224*N+21*signed+curvature) :
    0 ≤ 224*N+21*signed-V := by
  have h := same_response_combined_identity s z p b hidentity hcompatible hresponse
  nlinarith [sq_nonneg ‖s-(p+(3 : ℝ) • b)‖]

end KLSConstantImprovement.CompatibleHessianCombinedSquare
#print axioms KLSConstantImprovement.CompatibleHessianCombinedSquare.same_hessian_projection_identity
#print axioms KLSConstantImprovement.CompatibleHessianCombinedSquare.combined_square_identity
#print axioms KLSConstantImprovement.CompatibleHessianCombinedSquare.same_response_combined_identity
#print axioms KLSConstantImprovement.CompatibleHessianCombinedSquare.combined_energy_pays_additive_gate

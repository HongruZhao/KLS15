import Mathlib

/-! Exact finite shuffle square in the direct fully symmetric cubic source
primitive. Source PDE, BL domains, positive Gram gradient and contractions
are proved in the companion analytic note. No sign for the BL cross,
universal cubic6, or original-law additive completion is asserted. -/
noncomputable section
namespace KLSConstantImprovement.OriginalDirectTensorSourceCompensation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem tensor_shuffle_remainder_identity (u v : E) (hnorm : ‖v‖=‖u‖) :
    ‖u‖^2-inner ℝ u v = ‖u-v‖^2/2 := by
  rw [norm_sub_sq_real, hnorm]
  ring

theorem tensor_shuffle_remainder_nonneg (u v : E) (hnorm : ‖v‖=‖u‖) :
    0 ≤ ‖u‖^2-inner ℝ u v := by
  rw [tensor_shuffle_remainder_identity u v hnorm]
  positivity

theorem direct_tensor_signed_source_compensation {W p gamma energy D r : ℝ}
    (hsource : W=p+gamma+energy)
    (hBLcross : D=energy-W+r) :
    W+2*p+2*(gamma-energy/2)+3*D=3*r := by
  linarith

end KLSConstantImprovement.OriginalDirectTensorSourceCompensation
#print axioms KLSConstantImprovement.OriginalDirectTensorSourceCompensation.tensor_shuffle_remainder_identity
#print axioms KLSConstantImprovement.OriginalDirectTensorSourceCompensation.tensor_shuffle_remainder_nonneg
#print axioms KLSConstantImprovement.OriginalDirectTensorSourceCompensation.direct_tensor_signed_source_compensation

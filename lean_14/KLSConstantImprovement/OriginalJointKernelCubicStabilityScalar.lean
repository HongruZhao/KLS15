import KLSConstantImprovement.SandwichDeficitStabilityScalar

/-! Two-sided scalar payment for the new original unconditioned joint-H
moment-convergence bridge. Matrix PSD/domain and original deficit inputs
are explicit. This file does not formalize weak joint convergence,
conditional averaging, a Poisson field limit, or quadratic Jordan closure. -/
noncomputable section
namespace KLSConstantImprovement.OriginalJointKernelCubicStabilityScalar
set_option maxHeartbeats 2000000

theorem quadratic_deficit_pays_two_sided_bound {δ d b2 bop m3 M : ℝ}
    (hδ : 0 ≤ δ) (hd : 4*δ ≤ d) (hb2 : 0 ≤ b2) (hbop : 0 ≤ bop)
    (hjoint : |m3-6*M| ≤ 6*Real.sqrt (2*δ)*b2+3*δ*bop) :
    |m3-6*M| ≤ 3*Real.sqrt (2*d)*b2+(3/4 : ℝ)*d*bop := by
  have hd0 : 0 ≤ d := by linarith
  have hr0 := Real.sqrt_nonneg (2*δ)
  have hs0 := Real.sqrt_nonneg (2*d)
  have hr := Real.sq_sqrt (show 0 ≤ 2*δ by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ 2*d by positivity)
  have hroot : 2*Real.sqrt (2*δ) ≤ Real.sqrt (2*d) := by nlinarith
  have hp := mul_le_mul_of_nonneg_right hroot hb2
  have hq := mul_le_mul_of_nonneg_right hd hbop
  nlinarith

theorem sandwich_refined_original_two_sided {δ d c b2 bop m3 bc M : ℝ}
    (hδ : 0 ≤ δ) (hd : 4*δ ≤ d) (hc : 0 ≤ c)
    (hb2 : 0 ≤ b2) (hbop : 0 ≤ bop)
    (hdet : (m3-3*bc)^2 ≤ (9/2 : ℝ)*δ*c^2)
    (htrace : |bc-2*M| ≤ Real.sqrt (2*δ)*b2)
    (hnorm : c ≤ 2*b2+bop*Real.sqrt (2*δ)) :
    |m3-6*M| ≤ 3*Real.sqrt (2*d)*b2+(3/4 : ℝ)*d*bop := by
  apply quadratic_deficit_pays_two_sided_bound hδ hd hb2 hbop
  exact SandwichDeficitStabilityScalar.sandwich_refined_regular_bound
    hδ hc hb2 hbop hdet htrace hnorm

end KLSConstantImprovement.OriginalJointKernelCubicStabilityScalar
#print axioms KLSConstantImprovement.OriginalJointKernelCubicStabilityScalar.quadratic_deficit_pays_two_sided_bound
#print axioms KLSConstantImprovement.OriginalJointKernelCubicStabilityScalar.sandwich_refined_original_two_sided

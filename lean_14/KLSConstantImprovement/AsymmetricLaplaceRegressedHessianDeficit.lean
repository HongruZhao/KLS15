import KLSConstantImprovement.AsymmetricLaplaceResponseContraction

/-! Exact all-rate scalar asymmetric-Laplace Hessian calibration.
The actual canonical Stein kernel and natural form bindings are paper
inputs. These are family-only inequalities, not a post-affine spectral
gap for arbitrary fields or a new universal variance/Poincare bound. -/
noncomputable section
namespace KLSConstantImprovement.AsymmetricLaplaceRegressedHessianDeficit

theorem regressed_deficit_identity (r : ℝ) :
    r^2/(1+r^2)^2-2*r^3/(1+r^2)^3 =
      r^2*(1-r)^2/(1+r^2)^3 := by
  have hd : (1+r^2:ℝ) ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

theorem specific_hessian_post_affine_bounds {r : ℝ} (hr : 0 < r) :
    0 ≤ 2*r^3/(1+r^2)^3 ∧
    2*r^3/(1+r^2)^3 ≤ r^2/(1+r^2)^2 ∧
    2*(2*r^3/(1+r^2)^3) ≤ r^2*(1+r)^2/(1+r^2)^3 := by
  have hbalance := regressed_deficit_identity r
  have hnonneg : 0 ≤ r^2*(1-r)^2/(1+r^2)^3 := by positivity
  have henergy : r^2*(1+r)^2/(1+r^2)^3-
      2*r^3/(1+r^2)^3=r^2/(1+r^2)^2 := by
    have hd : (1+r^2:ℝ) ≠ 0 := ne_of_gt (by positivity)
    field_simp
    ring
  constructor
  · positivity
  constructor <;> nlinarith

end KLSConstantImprovement.AsymmetricLaplaceRegressedHessianDeficit
#print axioms KLSConstantImprovement.AsymmetricLaplaceRegressedHessianDeficit.regressed_deficit_identity
#print axioms KLSConstantImprovement.AsymmetricLaplaceRegressedHessianDeficit.specific_hessian_post_affine_bounds

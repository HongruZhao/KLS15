import Mathlib

/-! Finite consequences of the SAME shifted source spectral factor.
Actual closed-source spectral calculus, normalized BL top/bottom deficits,
exact Hessian variance and affine regression are explicit paper inputs.
No sign or final universal production/variance/Poincare cap is asserted. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.ShiftedFilterRegressedVarianceBudget

theorem spectral_tangent_factor {u mu : ℝ}
    (hu : 0 ≤ u) (hm : 0 ≤ mu) (hm2 : mu ≤ 2) :
    u / (u+2)^2 ≤ ((2-mu)*u+2*mu^2)/(mu+2)^3 := by
  have hu2 : 0 < u+2 := by linarith
  have hmpos : 0 < mu+2 := by linarith
  apply (div_le_div_iff₀ (pow_pos hu2 2) (pow_pos hmpos 3)).mpr
  have hp : 0 ≤ (u-mu)^2*((2-mu)*u+8) := by positivity
  have hi : (((2-mu)*u+2*mu^2)*(u+2)^2-u*(mu+2)^3) =
      (u-mu)^2*((2-mu)*u+8) := by ring
  nlinarith

theorem spectral_one_fifth_factor {u : ℝ} (hu : 0 ≤ u) :
    u/(u+2)^2 ≤ (225*u+10)/1331 := by
  have h := spectral_tangent_factor hu (by norm_num : (0:ℝ) ≤ 1/5)
    (by norm_num : (1/5:ℝ) ≤ 2)
  norm_num at h ⊢
  convert h using 1 <;> ring

theorem spectral_eighth_factor {u : ℝ} (hu : 0 ≤ u) :
    u/(u+2)^2 ≤ (1/8:ℝ) := by
  apply (div_le_iff₀ (pow_pos (show 0 < u+2 by linarith) 2)).mpr
  nlinarith [sq_nonneg (u-2)]

theorem finite_spectral_variance_bound {ι : Type*} [Fintype ι]
    (w u : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hu : ∀ i, 0 ≤ u i) :
    (∑ i, w i*(u i/(u i+2)^2)) ≤
      (225*(∑ i, w i*u i)+10*(∑ i, w i))/1331 := by
  have h : (∑ i, w i*(u i/(u i+2)^2)) ≤
      ∑ i, w i*((225*u i+10)/1331) := by
    exact Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (spectral_one_fifth_factor (hu i)) (hw i)
  have he : (∑ i, w i*((225*u i+10)/1331)) =
      (225*(∑ i, w i*u i)+10*(∑ i, w i))/1331 := by
    calc
      _ = ∑ i, ((225/1331:ℝ)*(w i*u i)+(10/1331:ℝ)*w i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        ring
  exact h.trans_eq he

theorem matched_cross_rational_variance_bound
    {c dg dh v f N delta affine r : ℝ}
    (hr : 0 ≤ r) (hdg : 0 ≤ dg) (hdh : 0 ≤ dh) (hv : 0 ≤ v)
    (hf : 0 ≤ f) (hCross : c^2 ≤ dg*f)
    (hFactor : f ≤ (225*dh+10*v)/1331)
    (hTop : dh ≤ delta/2) (hBottom : dg ≤ 2*r)
    (hVariance : v = N-delta-affine) :
    c^2 ≤ r*(20*N+205*delta-20*affine)/1331 := by
  have h1 := mul_le_mul_of_nonneg_left hFactor hdg
  have h2 := mul_le_mul_of_nonneg_right hBottom
    (show (0:ℝ) ≤ (225*dh+10*v)/1331 by positivity)
  have h3 := mul_le_mul_of_nonneg_left hTop hr
  nlinarith

theorem matched_cross_eighth_variance_bound
    {c dg v f N delta affine r : ℝ}
    (hr : 0 ≤ r) (hdg : 0 ≤ dg) (hv : 0 ≤ v)
    (hCross : c^2 ≤ dg*f) (hFactor : f ≤ v/8)
    (hBottom : dg ≤ 2*r) (hVariance : v = N-delta-affine) :
    c^2 ≤ r*(N-delta-affine)/4 := by
  have h1 := mul_le_mul_of_nonneg_left hFactor hdg
  have h2 := mul_le_mul_of_nonneg_right hBottom (show 0 ≤ v/8 by positivity)
  nlinarith

end KLSConstantImprovement.ShiftedFilterRegressedVarianceBudget
#print axioms KLSConstantImprovement.ShiftedFilterRegressedVarianceBudget.spectral_tangent_factor
#print axioms KLSConstantImprovement.ShiftedFilterRegressedVarianceBudget.spectral_one_fifth_factor
#print axioms KLSConstantImprovement.ShiftedFilterRegressedVarianceBudget.spectral_eighth_factor
#print axioms KLSConstantImprovement.ShiftedFilterRegressedVarianceBudget.finite_spectral_variance_bound
#print axioms KLSConstantImprovement.ShiftedFilterRegressedVarianceBudget.matched_cross_rational_variance_bound
#print axioms KLSConstantImprovement.ShiftedFilterRegressedVarianceBudget.matched_cross_eighth_variance_bound

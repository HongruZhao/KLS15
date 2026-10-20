import Mathlib

/-! Finite Hessian/curvature weights in the original-law critical cubic
variance tangent. The original density tilt, exact centering/whitening,
moment differentiation, and exponential integrations by parts are proved
on paper in the companion note. These finite statements do not assert
finite-deficit stability, a kernel derivative, or a universal law bound. -/
noncomputable section
namespace KLSConstantImprovement.OriginalCriticalVarianceCurvatureTangent

theorem variance_diagonal_weight_nonneg {t c : ℝ}
    (ht : 0 ≤ t) (hc : 0 ≤ c) :
    0 ≤ t^3*(6*t^2+39*t+192)*c := by
  have hp : 0 ≤ 6*t^2+39*t+192 := by nlinarith [sq_nonneg t]
  exact mul_nonneg (mul_nonneg (pow_nonneg ht 3) hp) hc

theorem additive_diagonal_weight_payment {t c : ℝ}
    (ht : 0 ≤ t) (hc : 0 ≤ c) :
    27*(t^3*(t+4)*c) ≤ t^3*(6*t^2+39*t+108)*c := by
  have hp : 0 ≤ 6*t^2+12*t := by nlinarith [sq_nonneg t]
  have h := mul_nonneg (mul_nonneg (pow_nonneg ht 3) hp) hc
  have heq : t^3*(6*t^2+39*t+108)*c - 27*(t^3*(t+4)*c) =
      t^3*(6*t^2+12*t)*c := by ring
  linarith

theorem finite_critical_variance_curvature_nonneg
    {ι : Type*} [Fintype ι] (a t : ι → ℝ) (H : ι → ι → ℝ)
    (ht : ∀ i, 0 ≤ t i) (hdiag : ∀ i, 0 ≤ H i i)
    (hPSD : ∀ z : ι → ℝ, 0 ≤ ∑ i, ∑ j, z i * H i j * z j) :
    0 ≤ (∑ i, ∑ j, (a i*(t i)^3) * H i j * (a j*(t j)^3)) +
      ∑ i, (a i)^2 * ((t i)^3*(6*(t i)^2+39*t i+192)*H i i) := by
  classical
  have hq := hPSD (fun i => a i*(t i)^3)
  have hs : 0 ≤ ∑ i, (a i)^2 * ((t i)^3*(6*(t i)^2+39*t i+192)*H i i) := by
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg (a i))
      (variance_diagonal_weight_nonneg (ht i) (hdiag i)))
  linarith

theorem finite_critical_additive_curvature_payment
    {ι : Type*} [Fintype ι] (a t : ι → ℝ) (H : ι → ι → ℝ)
    (ht : ∀ i, 0 ≤ t i) (hdiag : ∀ i, 0 ≤ H i i)
    (hPSD : ∀ z : ι → ℝ, 0 ≤ ∑ i, ∑ j, z i * H i j * z j) :
    27*(∑ i, (a i)^2 * ((t i)^3*(t i+4)*H i i)) ≤
      (∑ i, ∑ j, (a i*(t i)^3) * H i j * (a j*(t j)^3)) +
      ∑ i, (a i)^2 * ((t i)^3*(6*(t i)^2+39*t i+108)*H i i) := by
  classical
  have hq := hPSD (fun i => a i*(t i)^3)
  have hs : 27*(∑ i, (a i)^2 * ((t i)^3*(t i+4)*H i i)) ≤
      ∑ i, (a i)^2 * ((t i)^3*(6*(t i)^2+39*t i+108)*H i i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hi := mul_le_mul_of_nonneg_left
      (additive_diagonal_weight_payment (ht i) (hdiag i)) (sq_nonneg (a i))
    convert hi using 1 <;> ring
  linarith

end KLSConstantImprovement.OriginalCriticalVarianceCurvatureTangent
#print axioms KLSConstantImprovement.OriginalCriticalVarianceCurvatureTangent.variance_diagonal_weight_nonneg
#print axioms KLSConstantImprovement.OriginalCriticalVarianceCurvatureTangent.additive_diagonal_weight_payment
#print axioms KLSConstantImprovement.OriginalCriticalVarianceCurvatureTangent.finite_critical_variance_curvature_nonneg
#print axioms KLSConstantImprovement.OriginalCriticalVarianceCurvatureTangent.finite_critical_additive_curvature_payment

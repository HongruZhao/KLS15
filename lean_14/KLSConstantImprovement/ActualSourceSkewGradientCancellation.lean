import KLS.WeightedCompactSupport

/-! Actual compact-source skew cancellation for the scalar-compatible
quadratic filter. The measure is exp(-phi)dy, score is grad(phi), and the
test is an actual C2 compact scalar u. Weighted IBP, integrability and
Hessian symmetry are discharged; no moment-map/Poisson/domain hypothesis
is substituted. The noncompact same-response limit remains separate. -/
noncomputable section
open MeasureTheory Finset KLS
open scoped BigOperators ContDiff
namespace KLSConstantImprovement.ActualSourceSkewGradientCancellation

theorem skew_symmetric_contraction_zero {ι : Type*} [Fintype ι]
    (L U : Matrix ι ι ℝ)
    (hL : ∀ i j, L i j = -L j i)
    (hU : ∀ i j, U i j = U j i) :
    (∑ i, ∑ j, L i j * U i j) = 0 := by
  have hneg : (∑ i, ∑ j, L i j * U i j) =
      -(∑ i, ∑ j, L i j * U i j) := by
    calc
      _ = ∑ j, ∑ i, L i j * U i j := Finset.sum_comm
      _ = ∑ i, ∑ j, -(L i j * U i j) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [hL j i, hU j i]
        ring
      _ = _ := by simp only [Finset.sum_neg_distrib]
  linarith

/-- Compact support supplies every boundary/product integrability premise. -/
theorem source_score_gradient_coordinate {n : ℕ} {φ u : KLS.Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hu : ContDiff ℝ 2 u)
    (hc : HasCompactSupport u) (i j : Fin n) :
    (∫ x, coordinateDerivative φ j x * coordinateDerivative u i x
      ∂potentialMeasure φ) =
      ∫ x, coordinateHessian u x j i ∂potentialMeasure φ := by
  have hdi : ContDiff ℝ 1 (coordinateDerivative u i) :=
    contDiff_coordinateDerivative hu (by norm_num) i
  have hdφ : Continuous (coordinateDerivative φ j) :=
    (contDiff_coordinateDerivative hφ (m := 0) (by norm_num) j).continuous
  have hH : Continuous (fun x => coordinateHessian u x j i) :=
    (contDiff_coordinateHessian hu (m := 0) (by norm_num) j i).continuous
  have hdci := hasCompactSupport_coordinateDerivative hc i
  have hi := integrable_potentialMeasure_of_continuous_hasCompactSupport
    hφ.continuous hdi.continuous hdci
  have hhi := integrable_potentialMeasure_of_continuous_hasCompactSupport
    hφ.continuous hH (hasCompactSupport_coordinateHessian hc j i)
  have hprod := integrable_potentialMeasure_of_continuous_hasCompactSupport
    hφ.continuous (hdi.continuous.mul hdφ) hdci.mul_right
  have h := integral_mul_fderiv_potentialMeasure
    (f := fun _ : KLS.Space n => (1:ℝ)) (g := coordinateDerivative u i)
    (hφ.differentiable (by norm_num)) (differentiable_const (1:ℝ))
    (hdi.differentiable (by norm_num)) (EuclideanSpace.single j 1)
    (by simpa only [one_mul] using hi)
    (by simp [fderiv_const_apply])
    (by simpa only [one_mul, coordinateHessian, coordinateDerivative] using hhi)
    (by
      change Integrable (fun x => coordinateDerivative u i x * coordinateDerivative φ j x)
        (potentialMeasure φ) at hprod
      simpa only [one_mul, coordinateDerivative] using hprod)
  simp only [one_mul, fderiv_const_apply, ContinuousLinearMap.zero_apply,
    zero_mul, integral_zero, sub_zero] at h
  simpa only [coordinateDerivative, coordinateHessian, mul_comm] using h.symm

/-- A skew source score has zero pairing with every actual compact scalar
gradient. This is the exact skew removal used after scalar compatibility. -/
theorem compact_source_skew_gradient_zero {n : ℕ} {φ u : KLS.Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hu : ContDiff ℝ 2 u)
    (hc : HasCompactSupport u) (L : Matrix (Fin n) (Fin n) ℝ)
    (hL : ∀ i j, L i j = -L j i) :
    (∫ x, ∑ i : Fin n, ∑ j : Fin n,
      L i j * coordinateDerivative φ j x * coordinateDerivative u i x
      ∂potentialMeasure φ) = 0 := by
  have hdφ (j : Fin n) : Continuous (coordinateDerivative φ j) :=
    (contDiff_coordinateDerivative hφ (m := 0) (by norm_num) j).continuous
  have hdu (i : Fin n) : Continuous (coordinateDerivative u i) :=
    (contDiff_coordinateDerivative hu (m := 0) (by norm_num) i).continuous
  have hi (i j : Fin n) : Integrable (fun x =>
      L i j * coordinateDerivative φ j x * coordinateDerivative u i x)
      (potentialMeasure φ) := by
    simpa only [mul_assoc, Pi.mul_apply] using
      (integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
        ((hdφ j).mul (hdu i)) (hasCompactSupport_coordinateDerivative hc i).mul_left).const_mul (L i j)
  have hrow (i : Fin n) :
      (∫ x, ∑ j : Fin n,
        L i j * coordinateDerivative φ j x * coordinateDerivative u i x
        ∂potentialMeasure φ) =
      ∑ j : Fin n, L i j * (∫ x, coordinateHessian u x j i
        ∂potentialMeasure φ) := by
    rw [integral_finsetSum Finset.univ (fun j _ => hi i j)]
    apply Finset.sum_congr rfl
    intro j hj
    have heq : (fun x => L i j * coordinateDerivative φ j x * coordinateDerivative u i x) =
        (fun x => L i j * (coordinateDerivative φ j x * coordinateDerivative u i x)) := by
      funext x
      ring
    rw [heq, integral_const_mul, source_score_gradient_coordinate hφ hu hc]
  rw [integral_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))]
  simp_rw [hrow]
  apply skew_symmetric_contraction_zero L
    (fun i j => ∫ x, coordinateHessian u x j i ∂potentialMeasure φ) hL
  intro i j
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => (coordinateHessian_symmetric hu x).apply i j

end KLSConstantImprovement.ActualSourceSkewGradientCancellation
#print axioms KLSConstantImprovement.ActualSourceSkewGradientCancellation.skew_symmetric_contraction_zero
#print axioms KLSConstantImprovement.ActualSourceSkewGradientCancellation.source_score_gradient_coordinate
#print axioms KLSConstantImprovement.ActualSourceSkewGradientCancellation.compact_source_skew_gradient_zero

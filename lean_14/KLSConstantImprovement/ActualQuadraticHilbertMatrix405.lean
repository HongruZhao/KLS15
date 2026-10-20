import KLSConstantImprovement.ActualQuadraticResponseField405
import KLSConstantImprovement.ActualResponseWeightedEnergy405
import KLSConstantImprovement.ActualSourceNaturalWhitenedHessian405

/-! The literal row-whitened quadratic inverse matrix has global L2
entries without a quadratic mass hypothesis. It is a bounded-root
multiplier of the already constructed eta metric-gradient rows. -/
noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators
namespace KLSConstantImprovement.ActualQuadraticHilbertMatrix405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualWeakCanonicalMetricOrdinaryGraph ActualSourceQuadraticEta405
open ActualQuadraticResponseField405 ActualSourceNaturalGaffney405
open ActualSourceMetricFaithfulness405 ActualSourceNaturalWhitenedHessian405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

def actualQuadraticFluxMatrix (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i a => quadraticRowFlux d T i a x

def actualQuadraticWhiteMatrix (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  canonicalMetricUnroot d.potential x * actualQuadraticFluxMatrix d T x * canonicalMetricUnroot d.potential x

def actualQuadraticWhiteLp (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : Lp ℝ 2 (potentialMeasure d.potential) :=
  ∑ a, sourceUnrootMultiplier d a i (canonicalMetricGradient d.potential j (quadraticSourceEta d (T a)))

theorem actualQuadraticWhiteLp_coe (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (actualQuadraticWhiteLp d T i j : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      fun x => actualQuadraticWhiteMatrix d T x i j := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun a =>
    sourceUnrootMultiplier d a i (canonicalMetricGradient d.potential j (quadraticSourceEta d (T a)))),
    ae_all_iff.mpr (fun a => sourceUnrootMultiplier_coe d a i
      (canonicalMetricGradient d.potential j (quadraticSourceEta d (T a)))), d.hessian_ae_source] with x hs hm hx
  change (∑ a, sourceUnrootMultiplier d a i
    (canonicalMetricGradient d.potential j (quadraticSourceEta d (T a)))) x = _
  rw [hs]
  simp only [Finset.sum_apply, hm]
  let V : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun a r =>
    canonicalMetricGradient d.potential r (quadraticSourceEta d (T a)) x
  let R := canonicalMetricRoot d.potential x
  let S := canonicalMetricUnroot d.potential x
  have hR : R.IsSymm := inverseSqrtMatrix_isSymm _
  have hS : S.IsSymm := hR.inv
  have hRS : R * S = 1 := canonicalMetricRoot_mul_unroot_at hx.1
  have hu : V * R = actualQuadraticFluxMatrix d T x := by
    ext a r
    change (∑ b, V a b * R b r) = ∑ b, R r b * V a b
    apply Finset.sum_congr rfl
    intro b _
    rw [hR.apply r b]
    ring
  have hwhite : actualQuadraticWhiteMatrix d T x = S * V := by
    change S * actualQuadraticFluxMatrix d T x * S = _
    rw [← hu]
    simp only [Matrix.mul_assoc, hRS, Matrix.mul_one]
  rw [hwhite]
  change (∑ a, S a i * V a j) = ∑ a, S i a * V a j
  exact Finset.sum_congr rfl fun a _ => by rw [hS.apply i a]

theorem actualQuadraticWhiteMatrix_memLp (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    MemLp (fun x => actualQuadraticWhiteMatrix d T x i j) 2 (potentialMeasure d.potential) :=
  (memLp_congr_ae (actualQuadraticWhiteLp_coe d T i j)).mp (Lp.memLp _)

theorem frobenius_white_matrix (S A : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsSymm) :
    matrixFrobeniusSq (S * A * S) = ((S * S) * A * (S * S) * A.transpose).trace := by
  rw [matrixFrobeniusSq_eq_trace_mul_transpose]
  simp only [Matrix.transpose_mul, hS.eq]
  calc
    _ = (S * (A * (S * S) * A.transpose * S)).trace := by simp only [Matrix.mul_assoc]
    _ = ((A * (S * S) * A.transpose * S) * S).trace := Matrix.trace_mul_comm _ _
    _ = ((A * (S * S) * A.transpose) * (S * S)).trace := by simp only [Matrix.mul_assoc]
    _ = ((S * S) * (A * (S * S) * A.transpose)).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

def actualQuadraticMatrixCost (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  (coordinateHessian d.potential x * actualQuadraticFluxMatrix d T x *
    coordinateHessian d.potential x * (actualQuadraticFluxMatrix d T x).transpose).trace

theorem actual_quadratic_white_square_cost (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (fun x => matrixFrobeniusSq (actualQuadraticWhiteMatrix d T x))
      =ᵐ[potentialMeasure d.potential] actualQuadraticMatrixCost d T := by
  filter_upwards [d.hessian_ae_source] with x hx
  have hS : (canonicalMetricUnroot d.potential x).IsSymm := inverseSqrtMatrix_isSymm _ |>.inv
  have hSS := canonicalMetricUnroot_gram_at hx.1
  rw [hS.eq] at hSS
  rw [actualQuadraticWhiteMatrix, frobenius_white_matrix _ _ hS, hSS]
  rfl

theorem actual_quadratic_matrix_cost_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    Integrable (actualQuadraticMatrixCost d T) (potentialMeasure d.potential) :=
  (integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ fun j _ =>
    (actualQuadraticWhiteMatrix_memLp d T i j).integrable_sq)).congr (actual_quadratic_white_square_cost d T)

theorem actual_quadratic_Lp_norm_cost (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, ‖actualQuadraticWhiteLp d T i j‖ ^ 2) =
      ∫ x, actualQuadraticMatrixCost d T x ∂potentialMeasure d.potential := by
  simp_rw [L2.norm_sq_eq_integral_sq]
  have hi (i j : Fin n) : Integrable (fun x => actualQuadraticWhiteLp d T i j x ^ 2)
      (potentialMeasure d.potential) := (Lp.memLp _).integrable_sq
  have hrow (i : Fin n) : (∑ j, ∫ x, actualQuadraticWhiteLp d T i j x ^ 2 ∂potentialMeasure d.potential) =
      ∫ x, ∑ j, actualQuadraticWhiteLp d T i j x ^ 2 ∂potentialMeasure d.potential :=
    (integral_finsetSum Finset.univ fun j _ => hi i j).symm
  simp_rw [hrow]
  rw [← integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ fun j _ => hi i j)]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => actualQuadraticWhiteLp_coe d T i j,
    actual_quadratic_white_square_cost d T] with x hv hc
  simp only [hv]
  exact hc

end KLSConstantImprovement.ActualQuadraticHilbertMatrix405
#print axioms KLSConstantImprovement.ActualQuadraticHilbertMatrix405.actualQuadraticWhiteLp_coe
#print axioms KLSConstantImprovement.ActualQuadraticHilbertMatrix405.frobenius_white_matrix
#print axioms KLSConstantImprovement.ActualQuadraticHilbertMatrix405.actual_quadratic_matrix_cost_integrable
#print axioms KLSConstantImprovement.ActualQuadraticHilbertMatrix405.actual_quadratic_Lp_norm_cost

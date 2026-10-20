import KLSConstantImprovement.ActualAffineMatrixTests405

/-! Actual global affine score and Hessian balances. Every test below is
formed in the bounded X/H weak algebra; all global integrals and domain
passages are discharged on the constructed source. -/
noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualAffineGlobalBalance405
open KLS ActualBoundedCanonicalSource ActualCompactRawMetricGraph
open ActualBoundedRawTestAlgebra405 ActualQuarticHessianTest405
open ActualSourceHessianEvolution405 ActualSourceCurvatureDomains405
open ActualBoundedRawSourceCalculus405 ActualAffineMatrixTests405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

def actualAffineMainCost (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  (actualAffineMatrix d T x * coordinateHessian d.potential x *
    actualAffineMatrix d T x * coordinateHessian d.potential x).trace

def affineScoreTest (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : BoundedRawTest d :=
  rawTestSum fun a : Fin n => rawTestSum fun q : Fin n =>
    rawTestSum fun p : Fin n => rawTestSum fun b : Fin n =>
      (((BoundedRawTest.const d (T i a b)).mul (BoundedRawTest.hessian d b p)).mul
        (affineSliceTest d T p q)).mul (BoundedRawTest.hessian d q a)

theorem affineScoreTest_value (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (x : Space n) :
    (affineScoreTest d T i).value x =
      (T i * coordinateHessian d.potential x * actualAffineMatrix d T x *
        coordinateHessian d.potential x).trace := by
  change (∑ a, ∑ q, ∑ p, ∑ b,
    ((T i a b * coordinateHessian d.potential x b p) * (affineSliceTest d T p q).value x) *
      coordinateHessian d.potential x q a) = _
  simp only [affineSliceTest_value, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Finset.sum_mul]

theorem actual_affine_score_contraction (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) :
    actualAffineMainCost d T x = ∑ i, (affineScoreTest d T i).value x * gradient d.potential x i := by
  simp_rw [affineScoreTest_value]
  change ((∑ i, gradient d.potential x i • T i) * coordinateHessian d.potential x *
    actualAffineMatrix d T x * coordinateHessian d.potential x).trace = _
  simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem actual_affine_main_cost_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    Integrable (actualAffineMainCost d T) (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hi (i : Fin n) : Integrable (fun x => (affineScoreTest d T i).value x * gradient d.potential x i)
      (potentialMeasure d.potential) :=
    ((affineScoreTest d T i).value_top.mono_exponent (by simp : (2 : ℝ≥0∞) ≤ ∞)).integrable_mul
      (d.continuous_comp_gradient_memLp (EuclideanSpace.proj i).continuous 2)
  exact (integrable_finsetSum Finset.univ (fun i _ => hi i)).congr
    (Eventually.of_forall fun x => (actual_affine_score_contraction d T x).symm)

theorem actual_affine_global_score_balance (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (∫ x, actualAffineMainCost d T x ∂potentialMeasure d.potential) =
      ∑ i, ∫ x, (affineScoreTest d T i).derivative i x ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hi (i : Fin n) : Integrable (fun x => (affineScoreTest d T i).value x * gradient d.potential x i)
      (potentialMeasure d.potential) :=
    ((affineScoreTest d T i).value_top.mono_exponent (by simp : (2 : ℝ≥0∞) ≤ ∞)).integrable_mul
      (d.continuous_comp_gradient_memLp (EuclideanSpace.proj i).continuous 2)
  calc
    _ = ∫ x, ∑ i, (affineScoreTest d T i).value x * gradient d.potential x i
        ∂potentialMeasure d.potential :=
      integral_congr_ae (Eventually.of_forall (actual_affine_score_contraction d T))
    _ = _ := by
      rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
      exact Finset.sum_congr rfl fun i _ =>
        (ActualBoundedRawSourceCalculus405.BoundedRawTest.global_source_stein (affineScoreTest d T i) i).symm

def actualAffineMetricPair (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  ∑ i, ∑ j, ∑ r,
    rawCanonicalMetricDerivative d.potential (fun a y => d.third y a i j) r x *
      rawCanonicalMetricDerivative d.potential (affineHessianTest d T i j).derivative r x

theorem actual_affine_metric_pair_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    Integrable (actualAffineMetricPair d T) (potentialMeasure d.potential) :=
  integrable_finsetSum Finset.univ fun i _ => integrable_finsetSum Finset.univ fun j _ =>
    integrable_finsetSum Finset.univ fun r _ =>
      (d.hessian_entry_raw_metric_memLp i j r).integrable_mul
        ((affineHessianTest d T i j).metric_gradient r)

theorem actual_affine_global_hessian_balance (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    (∫ x, actualAffineMetricPair d T x ∂potentialMeasure d.potential) =
      (∫ x, actualAffineMainCost d T x ∂potentialMeasure d.potential) -
      ∫ x, ((actualAffineMatrix d T x * coordinateHessian d.potential x * actualAffineMatrix d T x) *
        sourceConnectionCurvature d x).trace ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hi (i j : Fin n) : Integrable (fun x => ∑ r,
      rawCanonicalMetricDerivative d.potential (fun a y => d.third y a i j) r x *
        rawCanonicalMetricDerivative d.potential (affineHessianTest d T i j).derivative r x)
      (potentialMeasure d.potential) := integrable_finsetSum Finset.univ fun r _ =>
    (d.hessian_entry_raw_metric_memLp i j r).integrable_mul ((affineHessianTest d T i j).metric_gradient r)
  have hprod (i j : Fin n) : Integrable (fun x =>
      (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) *
        (affineHessianTest d T i j).value x) (potentialMeasure d.potential) := by
    have hHC := ((d.hessian_entry_memLp i j 1).integrable le_rfl).sub
      (actual_connection_curvature_entry_integrable d i j)
    have hm : MemLp (fun x => (affineHessianTest d T i j).value x *
        (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j)) 1
        (potentialMeasure d.potential) := (affineHessianTest d T i j).value_top.mul
          (memLp_one_iff_integrable.mpr hHC)
    exact hm.integrable le_rfl |>.congr (Eventually.of_forall fun x => mul_comm _ _)
  have hleft : (∫ x, actualAffineMetricPair d T x ∂potentialMeasure d.potential) =
      ∑ i, ∑ j, ∫ x, (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) *
        (affineHessianTest d T i j).value x ∂potentialMeasure d.potential := by
    unfold actualAffineMetricPair
    rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ fun j _ => hi i j)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum Finset.univ (fun j _ => hi i j)]
    exact Finset.sum_congr rfl fun j _ => (affineHessianTest d T i j).global_hessian_test i j
  rw [hleft]
  have hrow (i : Fin n) :
      (∑ j, ∫ x, (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) *
        (affineHessianTest d T i j).value x ∂potentialMeasure d.potential) =
      ∫ x, ∑ j, (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) *
        (affineHessianTest d T i j).value x ∂potentialMeasure d.potential :=
    (integral_finsetSum Finset.univ (fun j _ => hprod i j)).symm
  simp_rw [hrow]
  rw [← integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ fun j _ => hprod i j)]
  have hinside : (fun x => ∑ i, ∑ j,
      (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) *
        (affineHessianTest d T i j).value x) =ᵐ[potentialMeasure d.potential]
      fun x => actualAffineMainCost d T x -
        ((actualAffineMatrix d T x * coordinateHessian d.potential x * actualAffineMatrix d T x) *
          sourceConnectionCurvature d x).trace := by
    filter_upwards [actual_affine_hessian_positive d T hT] with x hF
    simp only [affineHessianTest_value, sub_mul, Finset.sum_sub_distrib]
    rw [matrix_entrywise_contraction_eq_trace _ _ hF.isHermitian.isSymm,
      matrix_entrywise_contraction_eq_trace _ _ hF.isHermitian.isSymm]
    have he := Matrix.trace_mul_comm (coordinateHessian d.potential x)
      (actualAffineMatrix d T x * coordinateHessian d.potential x * actualAffineMatrix d T x)
    simpa only [Matrix.mul_assoc, actualAffineMainCost, Matrix.trace_mul_comm
      (sourceConnectionCurvature d x)] using congrArg
        (fun t : ℝ => t - (sourceConnectionCurvature d x *
          (actualAffineMatrix d T x * coordinateHessian d.potential x * actualAffineMatrix d T x)).trace) he
  rw [integral_congr_ae hinside, integral_sub (actual_affine_main_cost_integrable d T)
    (actual_affine_curvature_pair_integrable d T)]

end KLSConstantImprovement.ActualAffineGlobalBalance405
#print axioms KLSConstantImprovement.ActualAffineGlobalBalance405.actual_affine_main_cost_integrable
#print axioms KLSConstantImprovement.ActualAffineGlobalBalance405.actual_affine_global_score_balance
#print axioms KLSConstantImprovement.ActualAffineGlobalBalance405.actual_affine_metric_pair_integrable
#print axioms KLSConstantImprovement.ActualAffineGlobalBalance405.actual_affine_global_hessian_balance

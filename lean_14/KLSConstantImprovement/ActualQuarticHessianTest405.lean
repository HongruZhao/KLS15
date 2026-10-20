import KLSConstantImprovement.ActualBoundedRawTestAlgebra405
import KLSConstantImprovement.ActualQuarticPositiveGradient405

/-! The literal quartic matrix gradient is an actual bounded weak test
for the global source Hessian equation. Its raw derivative and all local
and global metric domains are constructed from the actual H and G fields.
The finite quartic commutator comparison remains a separate obligation. -/
noncomputable section
open MeasureTheory Matrix Set Filter
open scoped BigOperators ContDiff ENNReal
namespace KLSConstantImprovement.ActualQuarticHessianTest405
open KLS ActualBoundedCanonicalSource ActualCompactRawMetricGraph
open ActualBoundedRawTestAlgebra405 ActualSourceTensorGramMetricBinding
open ActualSourceHessianEvolution405 ActualSourceHessianPolynomialTests405
open ActualQuarticPositiveGradient405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)} {d : SourceData μ}

def rawTestSum {ι : Type*} [Fintype ι] (f : ι → BoundedRawTest d) : BoundedRawTest d where
  value := fun x => ∑ i, (f i).value x
  derivative := fun a x => ∑ i, (f i).derivative a x
  measurable := Finset.univ.aestronglyMeasurable_fun_sum fun i _ => (f i).measurable
  bounded := by
    let B : ι → ℝ := fun i => Classical.choose (f i).bounded
    have hb (i : ι) (x : Space n) : ‖(f i).value x‖ ≤ B i :=
      Classical.choose_spec (f i).bounded x
    exact ⟨∑ i, B i, fun x => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun i _ => hb i x)⟩
  derivative_local := fun a E hE =>
    memLp_finsetSum Finset.univ fun i _ => (f i).derivative_local a E hE
  weak_derivative := fun a => hasLocalWeakCoordinateDerivative_finset_sum Finset.univ
    (fun i _ => (f i).weak_derivative a)
    (fun i _ => locallyIntegrable_of_memLp_two_on_compacts (f i).value_local)
    (fun i _ => locallyIntegrable_of_memLp_two_on_compacts ((f i).derivative_local a))
  metric_gradient := by
    intro r
    have he : rawCanonicalMetricDerivative d.potential
        (fun a x => ∑ i, (f i).derivative a x) r =
      fun x => ∑ i, rawCanonicalMetricDerivative d.potential (f i).derivative r x := by
      funext x
      simp only [rawCanonicalMetricDerivative, Finset.mul_sum]
      exact Finset.sum_comm
    rw [he]
    exact memLp_finsetSum Finset.univ fun i _ => (f i).metric_gradient r

def tensorGramTest (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : BoundedRawTest d where
  value := sourceTensorGramEntry d.potential T i j
  derivative := sourceTensorGramRawDerivative d.potential d.third T i j
  measurable := by
    have hg : Continuous (fun H : Matrix (Fin n) (Fin n) ℝ => (T i * H * T j * H).trace) := by fun_prop
    have hm := (actual_hessian_polynomial_bounded d _ hg).1
    have he := funext (sourceTensorGramEntry_eq_trace d.potential T i j)
    exact he.symm ▸ hm
  bounded := by
    have hg : Continuous (fun H : Matrix (Fin n) (Fin n) ℝ => (T i * H * T j * H).trace) := by fun_prop
    obtain ⟨B, hb⟩ := (actual_hessian_polynomial_bounded d _ hg).2
    exact ⟨B, fun x => by rw [sourceTensorGramEntry_eq_trace]; exact hb x⟩
  derivative_local := fun a E hE => d.tensorGram_derivative_local_L2 T i j a E hE
  weak_derivative := fun a => d.tensorGram_hasLocalWeakCoordinateDerivative T i j a
  metric_gradient := d.tensorGram_raw_metric_memLp T i j

def quarticEntryTest (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) : BoundedRawTest d :=
  (BoundedRawTest.const d 2).mul (rawTestSum fun i : Fin n => rawTestSum fun j : Fin n =>
    rawTestSum fun q : Fin n => rawTestSum fun p : Fin n =>
      (BoundedRawTest.const d (T i a p * T j q b)).mul
        ((tensorGramTest d T i j).mul (BoundedRawTest.hessian d p q)))

theorem quarticEntryTest_value (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) (x : Space n) :
    (quarticEntryTest d T a b).value x =
      quarticMatrixGradient (coordinateHessian d.potential x) T a b := by
  change 2 * (∑ i, ∑ j, ∑ q, ∑ p, (T i a p * T j q b) *
    (sourceTensorGramEntry d.potential T i j x * coordinateHessian d.potential x p q)) = _
  simp only [quarticMatrixGradient, sliceMatrixContraction, Matrix.smul_apply,
    smul_eq_mul, Matrix.sum_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum,
    sourceTensorGramEntry_eq_trace, matrixTraceGram]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro p _
  have hc := Matrix.trace_mul_comm (coordinateHessian d.potential x)
    (T i * coordinateHessian d.potential x * T j)
  simp only [Matrix.mul_assoc] at hc ⊢
  rw [hc]
  ring

theorem actual_quartic_global_hessian_test (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (a b i j : Fin n) :
    (∫ x, ∑ r,
      rawCanonicalMetricDerivative d.potential (fun k y => d.third y k i j) r x *
        rawCanonicalMetricDerivative d.potential (quarticEntryTest d T a b).derivative r x
          ∂potentialMeasure d.potential) =
      ∫ x, (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) *
        quarticMatrixGradient (coordinateHessian d.potential x) T a b
          ∂potentialMeasure d.potential := by
  simpa only [quarticEntryTest_value] using (quarticEntryTest d T a b).global_hessian_test i j

end KLSConstantImprovement.ActualQuarticHessianTest405
#print axioms KLSConstantImprovement.ActualQuarticHessianTest405.rawTestSum
#print axioms KLSConstantImprovement.ActualQuarticHessianTest405.tensorGramTest
#print axioms KLSConstantImprovement.ActualQuarticHessianTest405.quarticEntryTest_value
#print axioms KLSConstantImprovement.ActualQuarticHessianTest405.actual_quartic_global_hessian_test

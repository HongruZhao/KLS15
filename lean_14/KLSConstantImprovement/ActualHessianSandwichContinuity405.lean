import KLSConstantImprovement.ActualSourceGramHalfBudget405
import KLSConstantImprovement.ActualMatchedFrame405

/-! Continuity in a constant matrix of the actual Hessian sandwich integral.
Only a finite quadratic polynomial of the same source moments is used. -/
noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators Topology MatrixOrder Matrix.Norms.L2Operator
namespace KLSConstantImprovement.ActualHessianSandwichContinuity405
open KLS ActualBoundedCanonicalSource ActualSourceMeanGramOrder405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem trace_sandwich_entry_expansion (A H : Matrix (Fin n) (Fin n) ℝ) :
    rawHessianTraceSquare H A =
      ∑ i, ∑ l, ∑ k, ∑ j, (A i j * A k l) * (H j k * H l i) := by
  simp only [rawHessianTraceSquare, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem actual_integral_sandwich_entry_polynomial (d : SourceData μ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (∫ x, rawHessianTraceSquare (coordinateHessian d.potential x) A
      ∂potentialMeasure d.potential) =
      ∑ i, ∑ l, ∑ k, ∑ j, (A i j * A k l) *
        ∫ x, coordinateHessian d.potential x j k * coordinateHessian d.potential x l i
          ∂potentialMeasure d.potential := by
  have hi (i l k j : Fin n) : Integrable (fun x => (A i j * A k l) *
      (coordinateHessian d.potential x j k * coordinateHessian d.potential x l i))
      (potentialMeasure d.potential) :=
    ((d.hessian_entry_memLp j k 2).integrable_mul (d.hessian_entry_memLp l i 2)).const_mul _
  simp_rw [trace_sandwich_entry_expansion]
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ fun l _ =>
    integrable_finsetSum Finset.univ fun k _ => integrable_finsetSum Finset.univ fun j _ => hi i l k j)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun l _ => integrable_finsetSum Finset.univ fun k _ =>
    integrable_finsetSum Finset.univ fun j _ => hi i l k j)]
  apply Finset.sum_congr rfl
  intro l _
  rw [integral_finsetSum Finset.univ (fun k _ => integrable_finsetSum Finset.univ fun j _ => hi i l k j)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_finsetSum Finset.univ (fun j _ => hi i l k j)]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

theorem actual_integral_sandwich_continuous (d : SourceData μ) :
    Continuous (fun A : Matrix (Fin n) (Fin n) ℝ =>
      ∫ x, rawHessianTraceSquare (coordinateHessian d.potential x) A
        ∂potentialMeasure d.potential) := by
  simp_rw [actual_integral_sandwich_entry_polynomial d]
  fun_prop

theorem coefficientGram_sqrt_regularized_tendsto (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT : ∀ i, (T i).IsSymm) :
    Tendsto (fun k => CFC.sqrt (cutoffScale k • (1 : Matrix (Fin n) (Fin n) ℝ) + sourceCoefficientGram T))
      atTop (𝓝 (CFC.sqrt (sourceCoefficientGram T))) := by
  have hQ : (sourceCoefficientGram T).PosSemidef := matrixTraceGram_posSemidef .one T hT
  have hp (k : ℕ) : (cutoffScale k • (1 : Matrix (Fin n) (Fin n) ℝ) + sourceCoefficientGram T).PosSemidef :=
    (Matrix.PosSemidef.one.smul (le_of_lt (cutoffScale_pos k))).add hQ
  have ht : Tendsto (fun k => cutoffScale k • (1 : Matrix (Fin n) (Fin n) ℝ) + sourceCoefficientGram T)
      atTop (𝓝 (sourceCoefficientGram T)) := by
    simpa using (cutoffScale_tendsto_zero.smul_const (1 : Matrix (Fin n) (Fin n) ℝ)).add_const
      (sourceCoefficientGram T)
  exact (CFC.continuousOn_sqrt (A := Matrix (Fin n) (Fin n) ℝ) (sourceCoefficientGram T) hQ.nonneg).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall fun k => (hp k).nonneg⟩)

theorem actual_regularized_gram_sandwich_tendsto (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    Tendsto (fun k => ∫ x, rawHessianTraceSquare (coordinateHessian d.potential x)
      (CFC.sqrt (cutoffScale k • (1 : Matrix (Fin n) (Fin n) ℝ) + sourceCoefficientGram T))
        ∂potentialMeasure d.potential) atTop
      (𝓝 (∫ x, rawHessianTraceSquare (coordinateHessian d.potential x)
        (CFC.sqrt (sourceCoefficientGram T)) ∂potentialMeasure d.potential)) :=
  (actual_integral_sandwich_continuous d).continuousAt.tendsto.comp
    (coefficientGram_sqrt_regularized_tendsto T hT)

end KLSConstantImprovement.ActualHessianSandwichContinuity405
#print axioms KLSConstantImprovement.ActualHessianSandwichContinuity405.actual_integral_sandwich_entry_polynomial
#print axioms KLSConstantImprovement.ActualHessianSandwichContinuity405.actual_integral_sandwich_continuous
#print axioms KLSConstantImprovement.ActualHessianSandwichContinuity405.coefficientGram_sqrt_regularized_tendsto
#print axioms KLSConstantImprovement.ActualHessianSandwichContinuity405.actual_regularized_gram_sandwich_tendsto

import KLSConstantImprovement.ActualGramHalf405
import KLSConstantImprovement.ActualSourceQuadraticSandwich405

/-!
The actual Gram-half deficit budget on the constructed canonical source.
All signed Hessian sandwich integrals are paid by the bounded actual H.
The quadratic cap is the proved actual-source cap. The pointwise Gram
half comparison uses the same H and the same constant slice family,
including singular Gram; no matrix-lift or deficit witness is supplied.
-/
noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators ENNReal MatrixOrder Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceGramHalfBudget405
open KLS ActualBoundedCanonicalSource ActualKroneckerGram405 ActualGramHalf405
open ActualSourceQuadraticSandwich405
variable {n : ℕ} {κ : Type*} [Fintype κ] {μ : Measure (Space n)}

theorem gramSqrt_frobeniusSq (T : κ → Matrix (Fin n) (Fin n) ℝ)
    (hT : ∀ i, (T i).IsSymm) :
    matrixFrobeniusSq (CFC.sqrt (sliceGram T)) = ∑ i, matrixFrobeniusSq (T i) := by
  have hG := sliceGram_posSemidef T hT
  have hA : (CFC.sqrt (sliceGram T)).IsSymm :=
    (CFC.sqrt_nonneg (sliceGram T)).posSemidef.isHermitian.isSymm
  rw [matrixFrobeniusSq_eq_trace_sq hA, CFC.sqrt_mul_sqrt_self _ hG.nonneg]
  change (∑ i, T i * T i).trace = ∑ i, matrixFrobeniusSq (T i)
  rw [Matrix.trace_sum]
  exact Finset.sum_congr rfl fun i _ => (matrixFrobeniusSq_eq_trace_sq (hT i)).symm

theorem actual_integral_gram_half_comparison (d : SourceData μ)
    (T : κ → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    (∫ x, ∑ i, (T i * coordinateHessian d.potential x * T i *
      coordinateHessian d.potential x).trace ∂potentialMeasure d.potential) ≤
    ∫ x, (CFC.sqrt (sliceGram T) * coordinateHessian d.potential x *
      CFC.sqrt (sliceGram T) * coordinateHessian d.potential x).trace
        ∂potentialMeasure d.potential := by
  have hI : Integrable (fun x => ∑ i, (T i * coordinateHessian d.potential x * T i *
      coordinateHessian d.potential x).trace) (potentialMeasure d.potential) :=
    integrable_finsetSum Finset.univ (fun i _ => d.signed_sandwich_integrable (T i))
  apply integral_mono_ae hI (d.signed_sandwich_integrable (CFC.sqrt (sliceGram T)))
  filter_upwards [d.hessian_ae_source] with x hx
  exact gram_half_trace_inequality T hT (coordinateHessian d.potential x) hx.1.isHermitian.isSymm

/-- The actual matched Gram-half deficit is nonnegative and at most
the actual sum of the original slice deficits, with their shared N. -/
theorem actual_gram_half_deficit_budget (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : κ → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    0 ≤ 2 * (∑ i, matrixFrobeniusSq (T i)) -
      (∫ x, (CFC.sqrt (sliceGram T) * coordinateHessian d.potential x *
        CFC.sqrt (sliceGram T) * coordinateHessian d.potential x).trace
          ∂potentialMeasure d.potential) ∧
    2 * (∑ i, matrixFrobeniusSq (T i)) -
      (∫ x, (CFC.sqrt (sliceGram T) * coordinateHessian d.potential x *
        CFC.sqrt (sliceGram T) * coordinateHessian d.potential x).trace
          ∂potentialMeasure d.potential) ≤
      2 * (∑ i, matrixFrobeniusSq (T i)) -
        (∫ x, ∑ i, (T i * coordinateHessian d.potential x * T i *
          coordinateHessian d.potential x).trace ∂potentialMeasure d.potential) := by
  have hA : (CFC.sqrt (sliceGram T)).IsSymm :=
    (CFC.sqrt_nonneg (sliceGram T)).posSemidef.isHermitian.isSymm
  have hcap := d.integral_signed_sandwich_le_two hiso (CFC.sqrt (sliceGram T)) hA
  rw [gramSqrt_frobeniusSq T hT] at hcap
  exact ⟨sub_nonneg.mpr hcap, sub_le_sub_left (actual_integral_gram_half_comparison d T hT) _⟩

/-- The actual nonnegative orientation gap is exactly the integral
of the finite Gram-half gap on the same source. -/
theorem actual_gram_half_gap_integral (d : SourceData μ)
    (T : κ → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    Integrable (fun x =>
      (CFC.sqrt (sliceGram T) * coordinateHessian d.potential x *
        CFC.sqrt (sliceGram T) * coordinateHessian d.potential x).trace -
      ∑ i, (T i * coordinateHessian d.potential x * T i * coordinateHessian d.potential x).trace)
      (potentialMeasure d.potential) ∧
    0 ≤ ∫ x,
      (CFC.sqrt (sliceGram T) * coordinateHessian d.potential x *
        CFC.sqrt (sliceGram T) * coordinateHessian d.potential x).trace -
      ∑ i, (T i * coordinateHessian d.potential x * T i * coordinateHessian d.potential x).trace
        ∂potentialMeasure d.potential := by
  have hleft := d.signed_sandwich_integrable (CFC.sqrt (sliceGram T))
  have hright : Integrable (fun x => ∑ i, (T i * coordinateHessian d.potential x * T i *
      coordinateHessian d.potential x).trace) (potentialMeasure d.potential) :=
    integrable_finsetSum Finset.univ (fun i _ => d.signed_sandwich_integrable (T i))
  refine ⟨hleft.sub hright, integral_nonneg_of_ae ?_⟩
  filter_upwards [d.hessian_ae_source] with x hx
  exact gram_half_gap_nonneg T hT (coordinateHessian d.potential x) hx.1.isHermitian.isSymm

end KLSConstantImprovement.ActualSourceGramHalfBudget405

#print axioms KLSConstantImprovement.ActualSourceGramHalfBudget405.gramSqrt_frobeniusSq
#print axioms KLSConstantImprovement.ActualSourceGramHalfBudget405.actual_integral_gram_half_comparison
#print axioms KLSConstantImprovement.ActualSourceGramHalfBudget405.actual_gram_half_deficit_budget
#print axioms KLSConstantImprovement.ActualSourceGramHalfBudget405.actual_gram_half_gap_integral

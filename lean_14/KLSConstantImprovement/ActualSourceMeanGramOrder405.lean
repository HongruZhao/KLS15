import KLSConstantImprovement.ActualSourceMeanGram405

/-! Literal Loewner bounds for the mean Gram of the constructed source.
Every scalar matrix-cap input is instantiated on an actual slice combination.
The matrix order is a conclusion; no source/kernel mean or positivity witness
is supplied.
-/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceMeanGramOrder405
open KLS ActualBoundedCanonicalSource ActualSourceMeanGram405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

def sourceCoefficientGram (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := matrixTraceGram 1 T

theorem sliceCombination_symmetric (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT : ∀ i, (T i).IsSymm) (v : Fin n → ℝ) : (sliceCombination T v).IsSymm := by
  change (∑ i, v i • T i).transpose = ∑ i, v i • T i
  simp only [Matrix.transpose_sum, Matrix.transpose_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [(hT i).eq]

theorem sourceCoefficientGram_quadratic (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT : ∀ i, (T i).IsSymm) (v : Fin n → ℝ) :
    v ⬝ᵥ (sourceCoefficientGram T *ᵥ v) = matrixFrobeniusSq (sliceCombination T v) := by
  rw [matrixFrobeniusSq_eq_trace_sq (sliceCombination_symmetric T hT v)]
  have hs := sliceCombination_trace (1 : Matrix (Fin n) (Fin n) ℝ) T v
  simp only [Matrix.mul_one] at hs
  rw [← hs]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, sourceCoefficientGram]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sourceMeanGram_isSymm (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    (sourceMeanGram d T).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  apply integral_congr_ae
  filter_upwards [d.hessian_ae_source] with x hx
  exact (matrixTraceGram_posSemidef hx.1.posSemidef T hT).isHermitian.isSymm.apply i j

private theorem sourceMeanGram_quadratic (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    v ⬝ᵥ (sourceMeanGram d T *ᵥ v) =
      ∫ x, (sliceCombination T v * coordinateHessian d.potential x *
        sliceCombination T v * coordinateHessian d.potential x).trace
          ∂potentialMeasure d.potential := by
  rw [← actual_meanGram_quadratic_identity]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem actual_meanGram_posSemidef (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    (sourceMeanGram d T).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_iff_isSymm.mpr (sourceMeanGram_isSymm d T hT))
  intro v
  simp only [star_trivial]
  rw [sourceMeanGram_quadratic]
  apply integral_nonneg_of_ae
  filter_upwards [d.hessian_ae_source] with x hx
  have hM := sliceCombination_symmetric T hT v
  have hp : (sliceCombination T v * coordinateHessian d.potential x *
      sliceCombination T v).PosSemidef := by
    simpa only [(Matrix.isHermitian_iff_isSymm.mpr hM).eq] using
      hx.1.posSemidef.conjTranspose_mul_mul_same (sliceCombination T v)
  exact trace_mul_nonneg_of_posSemidef hp hx.1.posSemidef

theorem actual_meanGram_le_two_coefficientGram (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    ((2 : ℝ) • sourceCoefficientGram T - sourceMeanGram d T).PosSemidef := by
  have hQ : (sourceCoefficientGram T).PosSemidef := matrixTraceGram_posSemidef .one T hT
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((hQ.smul (by norm_num : (0:ℝ) ≤ 2)).isHermitian.sub
      (Matrix.isHermitian_iff_isSymm.mpr (sourceMeanGram_isSymm d T hT)))
  intro v
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul, sourceCoefficientGram_quadratic T hT v]
  have hc := actual_meanGram_cap d hiso T hT v
  have he : v ⬝ᵥ (sourceMeanGram d T *ᵥ v) =
      ∑ i, ∑ j, v i * v j * sourceMeanGram d T i j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  linarith

end KLSConstantImprovement.ActualSourceMeanGramOrder405
#print axioms KLSConstantImprovement.ActualSourceMeanGramOrder405.sourceCoefficientGram_quadratic
#print axioms KLSConstantImprovement.ActualSourceMeanGramOrder405.actual_meanGram_posSemidef
#print axioms KLSConstantImprovement.ActualSourceMeanGramOrder405.actual_meanGram_le_two_coefficientGram

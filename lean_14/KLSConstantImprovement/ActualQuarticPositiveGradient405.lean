import KLSConstantImprovement.ActualSourceHessianPolynomialTests405
import KLS.PositiveMatrixSquareRoot

/-! Positive matrix gradient of the quartic tensor-Gram potential.
The finite sum-of-congruences proof applies to every symmetric family.
On the actual source its entries are bounded and every contraction with
the actual L1 curvature is integrable. -/
noncomputable section
open Matrix MeasureTheory Set Filter
open scoped BigOperators ContDiff ENNReal Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualQuarticPositiveGradient405
open KLS ActualBoundedCanonicalSource ActualSourceHessianEvolution405
open ActualSourceHessianPolynomialTests405 ActualSourceCurvatureDomains405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

def sliceMatrixContraction (H B : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i, ∑ j, B i j • (T i * H * T j)

theorem sliceMatrixContraction_posSemidef
    (H B : Matrix (Fin n) (Fin n) ℝ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosSemidef) (hB : B.PosSemidef) (hT : ∀ i, (T i).IsSymm) :
    (sliceMatrixContraction H B T).PosSemidef := by
  obtain ⟨R, hRs, hR⟩ := exists_symmetric_matrix_square_root hB
  let U : Fin n → Matrix (Fin n) (Fin n) ℝ := fun a => ∑ i, R a i • T i
  have hU (a : Fin n) : (U a).IsSymm := by
    change (∑ i, R a i • T i).transpose = ∑ i, R a i • T i
    simp only [Matrix.transpose_sum, Matrix.transpose_smul]
    exact Finset.sum_congr rfl fun i _ => by rw [(hT i).eq]
  have hBij (i j : Fin n) : B i j = ∑ a, R a i * R a j := by
    rw [← hR]
    rfl
  have he : sliceMatrixContraction H B T = ∑ a, U a * H * U a := by
    unfold sliceMatrixContraction
    simp_rw [hBij]
    simp only [Finset.sum_smul]
    have hswap : (∑ i, ∑ j, ∑ a, (R a i * R a j) • (T i * H * T j)) =
        ∑ a, ∑ i, ∑ j, (R a i * R a j) • (T i * H * T j) := by
      conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    rw [hswap]
    apply Finset.sum_congr rfl
    intro a _
    simp only [U, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
      Matrix.mul_smul, Finset.smul_sum, smul_smul]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm]
  rw [he]
  apply Matrix.posSemidef_sum
  intro a _
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, (hU a).eq] using
    hH.conjTranspose_mul_mul_same (U a)

def quarticMatrixGradient (H : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (2 : ℝ) • sliceMatrixContraction H (matrixTraceGram H T) T

theorem quarticMatrixGradient_posSemidef
    (H : Matrix (Fin n) (Fin n) ℝ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosSemidef) (hT : ∀ i, (T i).IsSymm) :
    (quarticMatrixGradient H T).PosSemidef :=
  (sliceMatrixContraction_posSemidef H (matrixTraceGram H T) T hH
    (matrixTraceGram_posSemidef hH T hT) hT).smul (by norm_num : (0 : ℝ) ≤ 2)

theorem actual_quartic_gradient_positive_ae (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      (quarticMatrixGradient (coordinateHessian d.potential x) T).PosSemidef := by
  filter_upwards [d.hessian_ae_source] with x hx
  exact quarticMatrixGradient_posSemidef _ T hx.1.posSemidef hT

theorem actual_quartic_gradient_entry_top (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    MemLp (fun x => quarticMatrixGradient (coordinateHessian d.potential x) T i j) ∞
      (potentialMeasure d.potential) := by
  let g : Matrix (Fin n) (Fin n) ℝ → ℝ := fun H => quarticMatrixGradient H T i j
  have hg : Continuous g := by
    dsimp [g, quarticMatrixGradient, sliceMatrixContraction, matrixTraceGram]
    fun_prop
  obtain ⟨hm, B, hb⟩ := actual_hessian_polynomial_bounded d g hg
  exact memLp_top_of_bound hm B (Eventually.of_forall hb)

theorem actual_quartic_curvature_pair_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun x => (quarticMatrixGradient (coordinateHessian d.potential x) T *
      sourceConnectionCurvature d x).trace) (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  change Integrable (fun x => ∑ i, ∑ j,
    quarticMatrixGradient (coordinateHessian d.potential x) T i j *
      sourceConnectionCurvature d x j i) (potentialMeasure d.potential)
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact ((actual_quartic_gradient_entry_top d T i j).mul
    (memLp_one_iff_integrable.mpr (actual_connection_curvature_entry_integrable d j i))).integrable le_rfl

theorem actual_quartic_curvature_pair_nonnegative (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    0 ≤ ∫ x, (quarticMatrixGradient (coordinateHessian d.potential x) T *
      sourceConnectionCurvature d x).trace ∂potentialMeasure d.potential := by
  apply integral_nonneg_of_ae
  filter_upwards [actual_quartic_gradient_positive_ae d T hT,
    actual_source_connection_curvature_positive d] with x hx hy
  exact trace_mul_nonneg_of_posSemidef hx hy

end KLSConstantImprovement.ActualQuarticPositiveGradient405
#print axioms KLSConstantImprovement.ActualQuarticPositiveGradient405.sliceMatrixContraction_posSemidef
#print axioms KLSConstantImprovement.ActualQuarticPositiveGradient405.actual_quartic_gradient_positive_ae
#print axioms KLSConstantImprovement.ActualQuarticPositiveGradient405.actual_quartic_curvature_pair_integrable
#print axioms KLSConstantImprovement.ActualQuarticPositiveGradient405.actual_quartic_curvature_pair_nonnegative

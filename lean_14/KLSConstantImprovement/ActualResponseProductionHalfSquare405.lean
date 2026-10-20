import KLSConstantImprovement.ActualResponseProductionAlgebra405

/-! A compatible-matrix Hilbert square pays half the literal response
error. The random row metric and the Poisson Jacobian are retained. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualResponseProductionHalfSquare405
open KLS ActualResponseProductionAlgebra405
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem compatibleTraceGram_parallelogram
    (A B : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    compatibleTraceGram (fun i => A i + B i) + compatibleTraceGram (fun i => A i - B i) =
      (2 : ℝ) • compatibleTraceGram A + (2 : ℝ) • compatibleTraceGram B := by
  ext i j
  simp only [compatibleTraceGram, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.trace_add, Matrix.trace_sub]
  ring

theorem weighted_compatible_half_difference_lower
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef)
    (A B : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (H * A i).IsSymm) (hB : ∀ i, (H * B i).IsSymm) :
    (H * compatibleTraceGram (fun i => A i - B i)).trace / 2 ≤
      (H * compatibleTraceGram A).trace + (H * compatibleTraceGram B).trace := by
  have hp : (compatibleTraceGram (fun i => A i + B i)).PosSemidef :=
    compatibleTraceGram_posSemidef H hH _ (fun i => by
      simpa only [Matrix.mul_add] using (hA i).add (hB i))
  have hn := trace_mul_nonneg_of_posSemidef hH.posSemidef hp
  have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => (H * M).trace)
    (compatibleTraceGram_parallelogram A B)
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul] at he
  linarith only [hn, he]

theorem response_production_half_square (H P F : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (N D T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ i, (N i).IsSymm) (hT : ∀ i, (T i).IsSymm)
    (hD : ∀ i, (H * D i).IsSymm) :
    (H * (F * P * F.transpose)).trace +
      (H * compatibleTraceGram (fun i => H⁻¹ * N i - (2 : ℝ) • (T i * H))).trace / 2 ≤
        (H * responseProductionMatrix H H⁻¹ P F N D T).trace := by
  have hHJ : H * H⁻¹ = 1 :=
    Matrix.mul_nonsing_inv H ((Matrix.isUnit_iff_isUnit_det _).mp hH.isUnit)
  have hc (i : Fin n) := completion_H_compatible H H⁻¹ (N i) (D i) (T i) hHJ
    hH.isHermitian.isSymm (hN i) (hT i) (hD i)
  have he := weighted_compatible_half_difference_lower H hH
    (fun i => completionLeft H H⁻¹ (N i) (D i) (T i))
    (fun i => completionRight H (D i) (T i)) (fun i => (hc i).1) (fun i => (hc i).2)
  have hdiff : (fun i => completionLeft H H⁻¹ (N i) (D i) (T i) -
      completionRight H (D i) (T i)) = fun i => H⁻¹ * N i - (2 : ℝ) • (T i * H) := by
    funext i
    simp only [completionLeft, completionRight]
    module
  rw [hdiff] at he
  simp only [responseProductionMatrix, Matrix.mul_add, Matrix.trace_add]
  linarith only [he]

end KLSConstantImprovement.ActualResponseProductionHalfSquare405
#print axioms KLSConstantImprovement.ActualResponseProductionHalfSquare405.compatibleTraceGram_parallelogram
#print axioms KLSConstantImprovement.ActualResponseProductionHalfSquare405.weighted_compatible_half_difference_lower
#print axioms KLSConstantImprovement.ActualResponseProductionHalfSquare405.response_production_half_square

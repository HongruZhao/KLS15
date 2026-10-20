import KLS.MatrixTracePositive

/-! Exact finite completion of the actual response production. The
Jacobian matrices need only be H-compatible, rather than Euclidean
symmetric. Their trace Gram is positive by genuine inverse-Hessian
congruence. No analytic production identity is assumed here. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualResponseProductionAlgebra405
open KLS
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def completionLeft (H J N D T : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  D + J * N - T * H

def completionRight (H D T : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := D + T * H

theorem response_production_completion (H J Nu Nv Du Dv Ti Tj : Matrix (Fin n) (Fin n) ℝ)
    (hHJ : H * J = 1) :
    (Ti * Nv).trace + (Tj * Nu).trace - (J * Nu * J * Nv).trace -
      2 * (Du * Dv).trace - ((Du * J * Nv).trace + (Dv * J * Nu).trace) =
      2 * (Ti * H * Tj * H).trace -
        ((completionLeft H J Nu Du Ti * completionLeft H J Nv Dv Tj).trace +
          (completionRight H Du Ti * completionRight H Dv Tj).trace) := by
  have hc (A B : Matrix (Fin n) (Fin n) ℝ) : (A * H * J * B).trace = (A * B).trace := by
    rw [Matrix.mul_assoc A H J, hHJ, Matrix.mul_one]
  have hn : (J * Nu * Tj * H).trace = (Tj * Nu).trace := by
    calc
      _ = (H * (J * Nu * Tj)).trace := Matrix.trace_mul_comm _ _
      _ = (Nu * Tj).trace := by
        simp only [← Matrix.mul_assoc, hHJ, Matrix.one_mul]
      _ = _ := Matrix.trace_mul_comm _ _
  have hcyc : (J * Nu * Dv).trace = (Dv * J * Nu).trace := by
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  simp only [completionLeft, completionRight, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub,
    Matrix.mul_add, Matrix.trace_sub, Matrix.trace_add, ← Matrix.mul_assoc]
  rw [hc Ti Nv, hn, hcyc]
  ring

def compatibleTraceGram (D : Fin n → Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (D i * D j).trace

theorem compatibleTraceGram_posSemidef (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef)
    (D : Fin n → Matrix (Fin n) (Fin n) ℝ) (hc : ∀ i, (H * D i).IsSymm) :
    (compatibleTraceGram D).PosSemidef := by
  have hJH : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H ((Matrix.isUnit_iff_isUnit_det _).mp hH.isUnit)
  have he (i : Fin n) : H⁻¹ * (H * D i) = D i := by rw [← Matrix.mul_assoc, hJH, Matrix.one_mul]
  have hg : compatibleTraceGram D = matrixTraceGram H⁻¹ (fun i => H * D i) := by
    ext i j
    change (D i * D j).trace = (H⁻¹ * (H * D i) * H⁻¹ * (H * D j)).trace
    calc
      _ = ((H⁻¹ * (H * D i)) * (H⁻¹ * (H * D j))).trace := by rw [he i, he j]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [hg]
  exact matrixTraceGram_posSemidef hH.posSemidef.inv _ hc

theorem completion_H_compatible (H J N D T : Matrix (Fin n) (Fin n) ℝ)
    (hHJ : H * J = 1) (hH : H.IsSymm) (hN : N.IsSymm) (hT : T.IsSymm)
    (hD : (H * D).IsSymm) :
    (H * completionLeft H J N D T).IsSymm ∧ (H * completionRight H D T).IsSymm := by
  have ht : (H * T * H).IsSymm := by
    change (H * T * H).transpose = _
    simp only [Matrix.transpose_mul, hH.eq, hT.eq, Matrix.mul_assoc]
  have hl : H * completionLeft H J N D T = H * D + N - H * T * H := by
    simp only [completionLeft, Matrix.mul_sub, Matrix.mul_add, ← Matrix.mul_assoc,
      hHJ, Matrix.one_mul]
  have hr : H * completionRight H D T = H * D + H * T * H := by
    simp only [completionRight, Matrix.mul_add, Matrix.mul_assoc]
  constructor
  · rw [hl]
    change (H * D + N - H * T * H).transpose = _
    rw [Matrix.transpose_sub, Matrix.transpose_add, hD.eq, hN.eq, ht.eq]
  · rw [hr]
    change (H * D + H * T * H).transpose = _
    rw [Matrix.transpose_add, hD.eq, ht.eq]

def responseProductionMatrix (H J P F : Matrix (Fin n) (Fin n) ℝ)
    (N D T : Fin n → Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  F * P * F.transpose + compatibleTraceGram (fun i => completionLeft H J (N i) (D i) (T i)) +
    compatibleTraceGram (fun i => completionRight H (D i) (T i))

theorem responseProductionMatrix_posSemidef (H P F : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (hP : P.PosSemidef)
    (N D T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ i, (N i).IsSymm) (hT : ∀ i, (T i).IsSymm) (hD : ∀ i, (H * D i).IsSymm) :
    (responseProductionMatrix H H⁻¹ P F N D T).PosSemidef := by
  have hHJ : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H ((Matrix.isUnit_iff_isUnit_det _).mp hH.isUnit)
  have hc (i : Fin n) := completion_H_compatible H H⁻¹ (N i) (D i) (T i) hHJ
    hH.isHermitian.isSymm (hN i) (hT i) (hD i)
  have hFP : (F * P * F.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using
      hP.conjTranspose_mul_mul_same F.transpose
  exact (hFP.add (compatibleTraceGram_posSemidef H hH _ (fun i => (hc i).1))).add
    (compatibleTraceGram_posSemidef H hH _ (fun i => (hc i).2))

end KLSConstantImprovement.ActualResponseProductionAlgebra405

#print axioms KLSConstantImprovement.ActualResponseProductionAlgebra405.response_production_completion
#print axioms KLSConstantImprovement.ActualResponseProductionAlgebra405.compatibleTraceGram_posSemidef
#print axioms KLSConstantImprovement.ActualResponseProductionAlgebra405.responseProductionMatrix_posSemidef

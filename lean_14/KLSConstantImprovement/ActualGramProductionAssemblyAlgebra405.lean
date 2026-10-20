import KLS.MatrixTracePositive

/-! Exact finite assembly of two ordinary row equations and the weak
source-Hessian equation. This retains the signed mixed Jacobian trace
and connection contraction until the positive completion is applied. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualGramProductionAssemblyAlgebra405
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def mixedRowDrift (H Du Dv : Matrix (Fin n) (Fin n) ℝ) (g u v : Fin n → ℝ) : ℝ :=
  ∑ a, (v a * (g a - ∑ r, H r a * u r) - ∑ r, Du r a * Dv a r)

def mixedHessianDrift (H S : Matrix (Fin n) (Fin n) ℝ)
    (K : Fin n → Fin n → Fin n → ℝ) (Du Dv : Matrix (Fin n) (Fin n) ℝ)
    (u v : Fin n → ℝ) : ℝ :=
  ∑ a, ∑ b, ((u a * v b) * (H a b - S a b) -
    ∑ r, K a b r * (Du a r * v b + u a * Dv b r))

theorem mixed_row_drift_expansion (H Du Dv : Matrix (Fin n) (Fin n) ℝ) (g u v : Fin n → ℝ) :
    mixedRowDrift H Du Dv g u v = g ⬝ᵥ v - u ⬝ᵥ (H *ᵥ v) - (Du * Dv).trace := by
  have hg : (∑ a, v a * g a) = g ⬝ᵥ v := Finset.sum_congr rfl fun a _ => mul_comm _ _
  have hh : (∑ a, ∑ r, v a * (H r a * u r)) = u ⬝ᵥ (H *ᵥ v) := by
    rw [Finset.sum_comm]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun a _ => by ring
  have hq : (∑ a, ∑ r, Du r a * Dv a r) = (Du * Dv).trace := by
    rw [Finset.sum_comm]
    rfl
  simp only [mixedRowDrift, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hg, hh, hq]

theorem mixed_hessian_drift_expansion (H S : Matrix (Fin n) (Fin n) ℝ)
    (K : Fin n → Fin n → Fin n → ℝ) (Du Dv : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ) :
    mixedHessianDrift H S K Du Dv u v =
      u ⬝ᵥ (H *ᵥ v) - u ⬝ᵥ (S *ᵥ v) -
        ∑ a, ∑ b, ∑ r, K a b r * (Du a r * v b + u a * Dv b r) := by
  have hp (A : Matrix (Fin n) (Fin n) ℝ) : (∑ a, ∑ b, (u a * v b) * A a b) = u ⬝ᵥ (A *ᵥ v) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  simp only [mixedHessianDrift, mul_sub, Finset.sum_sub_distrib]
  rw [hp H, hp S]

theorem assembled_drift_expansion (H S Du Dv : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.IsSymm) (K : Fin n → Fin n → Fin n → ℝ) (g h u v : Fin n → ℝ) :
    mixedRowDrift H Du Dv g u v + mixedRowDrift H Dv Du h v u +
      mixedHessianDrift H S K Du Dv u v =
      (∑ a, (g a * v a + u a * h a)) - u ⬝ᵥ (H *ᵥ v) - u ⬝ᵥ (S *ᵥ v) -
        2 * (Du * Dv).trace -
          ∑ a, ∑ b, ∑ r, K a b r * (Du a r * v b + u a * Dv b r) := by
  rw [mixed_row_drift_expansion, mixed_row_drift_expansion, mixed_hessian_drift_expansion,
    hH.dotProduct_mulVec_comm (x := v) (y := u), Matrix.trace_mul_comm Dv Du,
    dotProduct_comm h u]
  simp only [Finset.sum_add_distrib, dotProduct]
  ring

end KLSConstantImprovement.ActualGramProductionAssemblyAlgebra405

#print axioms KLSConstantImprovement.ActualGramProductionAssemblyAlgebra405.mixed_row_drift_expansion
#print axioms KLSConstantImprovement.ActualGramProductionAssemblyAlgebra405.assembled_drift_expansion

import KLSConstantImprovement.ActualMatchedFormInvariance405

/-! Constant matrix congruence preserves a summed scalar bilinear
pairing, including pairings that contain a fixed scalar resolvent. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualBilinearMatrixCongruence405
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def linearFamilyMix (A : Matrix ι ι ℝ) (U : ι → H) (i : ι) : H :=
  ∑ a, A i a • U a

theorem bilinear_family_mix (C : H →L[ℝ] H →L[ℝ] ℝ)
    (A B : Matrix ι ι ℝ) (U V : ι → H) :
    (∑ i, C (linearFamilyMix A U i) (linearFamilyMix B V i)) =
      ∑ a, ∑ b, (A.transpose * B) a b * C (U a) (V b) := by
  have hp (i : ι) : C (linearFamilyMix A U i) (linearFamilyMix B V i) =
      ∑ a, ∑ b, (A i a * B i b) * C (U a) (V b) := by
    simp only [linearFamilyMix, map_sum, map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp only [hp, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

def matrixCongruenceCoefficients (R S : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ :=
  fun p q => R p.1 q.1 * S q.2 p.2

def linearMatrixCongruence (R : Matrix (Fin n) (Fin n) ℝ)
    (U : Fin n → Fin n → H) (S : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : H :=
  linearFamilyMix (matrixCongruenceCoefficients R S) (fun p => U p.1 p.2) (i,j)

theorem dual_congruence_coefficient_identity (R S : Matrix (Fin n) (Fin n) ℝ) (hSR : S * R = 1) :
    (matrixCongruenceCoefficients R R.transpose).transpose *
      matrixCongruenceCoefficients S.transpose S = 1 := by
  ext p q
  have hf : ((matrixCongruenceCoefficients R R.transpose).transpose *
      matrixCongruenceCoefficients S.transpose S) p q = (S * R) q.1 p.1 * (S * R) q.2 p.2 := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, matrixCongruenceCoefficients,
      Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hf, hSR]
  rcases p with ⟨a,b⟩
  rcases q with ⟨c,e⟩
  change (1 : Matrix (Fin n) (Fin n) ℝ) c a * (1 : Matrix (Fin n) (Fin n) ℝ) e b =
    (1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ) (a,b) (c,e)
  simp only [Matrix.one_apply]
  by_cases hca : c = a <;> by_cases heb : e = b <;> simp [hca, heb, Prod.ext_iff] <;> aesop

theorem bilinear_dual_matrix_congruence (C : H →L[ℝ] H →L[ℝ] ℝ)
    (R S : Matrix (Fin n) (Fin n) ℝ) (hSR : S * R = 1)
    (U V : Fin n → Fin n → H) :
    (∑ i, ∑ j, C (linearMatrixCongruence R U R.transpose i j)
      (linearMatrixCongruence S.transpose V S i j)) = ∑ i, ∑ j, C (U i j) (V i j) := by
  have hm := bilinear_family_mix C (matrixCongruenceCoefficients R R.transpose)
    (matrixCongruenceCoefficients S.transpose S) (fun p => U p.1 p.2) (fun p => V p.1 p.2)
  rw [dual_congruence_coefficient_identity R S hSR] at hm
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true] at hm
  simpa only [linearMatrixCongruence, Fintype.sum_prod_type] using hm

end KLSConstantImprovement.ActualBilinearMatrixCongruence405

#print axioms KLSConstantImprovement.ActualBilinearMatrixCongruence405.bilinear_family_mix
#print axioms KLSConstantImprovement.ActualBilinearMatrixCongruence405.dual_congruence_coefficient_identity
#print axioms KLSConstantImprovement.ActualBilinearMatrixCongruence405.bilinear_dual_matrix_congruence

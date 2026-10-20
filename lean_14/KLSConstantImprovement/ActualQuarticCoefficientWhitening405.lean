import KLSConstantImprovement.ActualQuarticThirdWhitening405

/-! Exact coefficient-index contractions. These use the actual entries
of RᵀR and finite sums; the row space and its Hilbert--Schmidt pairing
are kept fixed. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualQuarticCoefficientWhitening405
open ActualQuarticCompression405 ActualQuarticWhiteFrame405
open ActualQuarticCongruence405 ActualQuarticThirdWhitening405
variable {ι κ p q : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [Fintype p] [Fintype q]
set_option maxHeartbeats 1500000

def mixRectFamily (R : Matrix ι ι ℝ) (U : ι → Matrix p q ℝ) : ι → Matrix p q ℝ :=
  fun l => ∑ a, R l a • U a

theorem entryPair_mix (R : Matrix ι ι ℝ) (U : ι → Matrix p q ℝ) (l m : ι) :
    entryPair (mixRectFamily R U l) (mixRectFamily R U m) =
      ∑ a, ∑ b, (R l a * R m b) * entryPair (U a) (U b) := by
  simp only [mixRectFamily, entryPair_eq_trace, Matrix.transpose_sum, Matrix.transpose_smul,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem entrySquare_eq_pair (A : Matrix p q ℝ) : entrySquare A = entryPair A A := by
  simp only [entrySquare, entryPair, pow_two]

theorem sum_entrySquare_mix (R : Matrix ι ι ℝ) (U : ι → Matrix p q ℝ) :
    (∑ l, entrySquare (mixRectFamily R U l)) =
      ∑ a, ∑ b, (R.transpose * R) a b * entryPair (U a) (U b) := by
  simp only [entrySquare_eq_pair, entryPair_mix, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_comm

theorem rawGramDerivative_mix (H : Matrix ι ι ℝ) (T : κ → Matrix ι ι ℝ)
    (R : Matrix ι ι ℝ) (N : ι → Matrix ι ι ℝ) (l : ι) :
    rawGramDerivative H T (mixFamily R N l) =
      mixRectFamily R (fun a => rawGramDerivative H T (N a)) l := by
  ext i j
  simp only [rawGramDerivative, mixFamily, mixRectFamily,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_sum, Matrix.trace_smul, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, mul_add, Finset.sum_add_distrib]

theorem raw_derivative_energy_whitening (H : Matrix ι ι ℝ) (T : κ → Matrix ι ι ℝ)
    (R : Matrix ι ι ℝ) (N : ι → Matrix ι ι ℝ) :
    (∑ a, ∑ b, (R.transpose * R) a b *
      entryPair (rawGramDerivative H T (N a)) (rawGramDerivative H T (N b))) =
      ∑ l, entrySquare (rawGramDerivative H T (mixFamily R N l)) := by
  simp only [rawGramDerivative_mix]
  exact (sum_entrySquare_mix R (fun a => rawGramDerivative H T (N a))).symm

theorem rawGramSecond_sum_left {ρ : Type*} [Fintype ρ]
    (T : κ → Matrix ι ι ℝ) (C : ρ → Matrix ι ι ℝ) (D : Matrix ι ι ℝ) :
    rawGramSecond T (∑ a, C a) D = ∑ a, rawGramSecond T (C a) D := by
  ext i j
  simp only [rawGramSecond, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum,
    Matrix.sum_apply, Finset.sum_add_distrib]

theorem rawGramSecond_sum_right {ρ : Type*} [Fintype ρ]
    (T : κ → Matrix ι ι ℝ) (C : Matrix ι ι ℝ) (D : ρ → Matrix ι ι ℝ) :
    rawGramSecond T C (∑ b, D b) = ∑ b, rawGramSecond T C (D b) := by
  ext i j
  simp only [rawGramSecond, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum,
    Matrix.sum_apply, Finset.sum_add_distrib]

theorem rawGramSecond_smul_left (T : κ → Matrix ι ι ℝ)
    (C D : Matrix ι ι ℝ) (c : ℝ) :
    rawGramSecond T (c • C) D = c • rawGramSecond T C D := by
  ext i j
  simp only [rawGramSecond, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_smul, Matrix.smul_apply, smul_eq_mul]
  ring

theorem rawGramSecond_smul_right (T : κ → Matrix ι ι ℝ)
    (C D : Matrix ι ι ℝ) (c : ℝ) :
    rawGramSecond T C (c • D) = c • rawGramSecond T C D := by
  ext i j
  simp only [rawGramSecond, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_smul, Matrix.smul_apply, smul_eq_mul]
  ring

theorem rawGramSecond_mix (T : κ → Matrix ι ι ℝ)
    (R : Matrix ι ι ℝ) (N : ι → Matrix ι ι ℝ) (l m : ι) :
    rawGramSecond T (mixFamily R N l) (mixFamily R N m) =
      ∑ a, ∑ b, (R l a * R m b) • rawGramSecond T (N a) (N b) := by
  simp only [mixFamily, rawGramSecond_sum_left, rawGramSecond_sum_right,
    rawGramSecond_smul_left, rawGramSecond_smul_right, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_comm (R m b) (R l a)]

theorem raw_second_contraction_whitening (G : Matrix κ κ ℝ)
    (T : κ → Matrix ι ι ℝ) (R : Matrix ι ι ℝ) (N : ι → Matrix ι ι ℝ) :
    (∑ a, ∑ b, (R.transpose * R) a b * entryPair G (rawGramSecond T (N a) (N b))) =
      ∑ l, entryPair G (rawGramSecond T (mixFamily R N l) (mixFamily R N l)) := by
  symm
  simp only [rawGramSecond_mix, entryPair_eq_trace, Matrix.mul_sum, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_comm

end KLSConstantImprovement.ActualQuarticCoefficientWhitening405

#print axioms KLSConstantImprovement.ActualQuarticCoefficientWhitening405.sum_entrySquare_mix
#print axioms KLSConstantImprovement.ActualQuarticCoefficientWhitening405.raw_derivative_energy_whitening
#print axioms KLSConstantImprovement.ActualQuarticCoefficientWhitening405.rawGramSecond_mix
#print axioms KLSConstantImprovement.ActualQuarticCoefficientWhitening405.raw_second_contraction_whitening

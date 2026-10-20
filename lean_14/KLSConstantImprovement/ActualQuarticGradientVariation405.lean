import KLSConstantImprovement.ActualQuarticCongruence405

/-! Exact finite variation of the quartic matrix gradient. This will
identify the literal weak A4 derivative pairing with E4+HessG, so the
global quartic estimate needs no separate HessG integrability premise. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualQuarticGradientVariation405
open ActualQuarticCompression405 ActualQuarticCongruence405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

private theorem trace_swap_four (A B C D : Matrix ι ι ℝ) :
    (A * B * C * D).trace = (C * D * A * B).trace := by
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (A * B) (C * D)

theorem rawGram_symmetric (H : Matrix ι ι ℝ) (T : κ → Matrix ι ι ℝ) :
    (rawGram H T).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact trace_swap_four (T j) H (T i) H

theorem rawGramDerivative_symmetric (H C : Matrix ι ι ℝ)
    (T : κ → Matrix ι ι ℝ) : (rawGramDerivative H T C).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  change (T j * C * T i * H).trace + (T j * H * T i * C).trace =
    (T i * C * T j * H).trace + (T i * H * T j * C).trace
  rw [trace_swap_four (T j) C (T i) H, trace_swap_four (T j) H (T i) C]
  ring

def weightedSlice (H : Matrix ι ι ℝ) (T : κ → Matrix ι ι ℝ)
    (B : Matrix κ κ ℝ) : Matrix ι ι ℝ := ∑ i, ∑ j, B i j • (T i * H * T j)

theorem weightedSlice_pair (H A : Matrix ι ι ℝ) (T : κ → Matrix ι ι ℝ)
    (B : Matrix κ κ ℝ) (hB : B.IsSymm) :
    2 * (A * weightedSlice H T B).trace = entryPair B (rawGramDerivative H T A) := by
  have hw : (∑ i, ∑ j, B i j * (T i * A * T j * H).trace) =
      ∑ i, ∑ j, B i j * (T i * H * T j * A).trace := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hB.apply i j, trace_swap_four (T j) A (T i) H]
  have ht : (A * weightedSlice H T B).trace =
      ∑ i, ∑ j, B i j * (T i * H * T j * A).trace := by
    simp only [weightedSlice, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
      Matrix.trace_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have he := Matrix.trace_mul_comm A (T i * H * T j)
    simp only [Matrix.mul_assoc] at he ⊢
    rw [he]
  rw [ht]
  unfold entryPair rawGramDerivative
  simp only [mul_add, Finset.sum_add_distrib]
  rw [hw]
  ring

def rawQuarticGradientVariation (H : Matrix ι ι ℝ)
    (T : κ → Matrix ι ι ℝ) (C : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (2 : ℝ) • weightedSlice H T (rawGramDerivative H T C) +
    (2 : ℝ) • weightedSlice C T (rawGram H T)

theorem quartic_gradient_variation_pair (H A B : Matrix ι ι ℝ)
    (T : κ → Matrix ι ι ℝ) :
    (A * rawQuarticGradientVariation H T B).trace =
      entryPair (rawGramDerivative H T A) (rawGramDerivative H T B) +
        entryPair (rawGram H T) (rawGramSecond T A B) := by
  simp only [rawQuarticGradientVariation, Matrix.mul_add, Matrix.trace_add,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [weightedSlice_pair H A T _ (rawGramDerivative_symmetric H B T),
    weightedSlice_pair B A T _ (rawGram_symmetric H T)]
  have hc : entryPair (rawGramDerivative H T B) (rawGramDerivative H T A) =
      entryPair (rawGramDerivative H T A) (rawGramDerivative H T B) := by
    unfold entryPair
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hc]
  rfl

end KLSConstantImprovement.ActualQuarticGradientVariation405
#print axioms KLSConstantImprovement.ActualQuarticGradientVariation405.weightedSlice_pair
#print axioms KLSConstantImprovement.ActualQuarticGradientVariation405.quartic_gradient_variation_pair

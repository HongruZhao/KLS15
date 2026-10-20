import KLSConstantImprovement.ActualDirectCubicWhitening405

/-! The source inverse-metric cross energy is exactly twice the direct
tetrahedral half-cross, with the coefficient index whitened literally. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualDirectCubicCoefficients405
open KLS ActualQuarticCompression405 ActualQuarticCongruence405
open ActualQuarticThirdWhitening405 ActualQuarticCoefficientWhitening405
open ActualDirectCubicWhitening405
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem entryPair_mix_two (R : Matrix (Fin n) (Fin n) ℝ)
    (U V : Fin n → Matrix (Fin n) (Fin n) ℝ) (l m : Fin n) :
    entryPair (mixRectFamily R U l) (mixRectFamily R V m) =
      ∑ a, ∑ b, (R l a * R m b) * entryPair (U a) (V b) := by
  simp only [mixRectFamily, entryPair_eq_trace, Matrix.transpose_sum, Matrix.transpose_smul,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem sum_entryPair_mix_two (R : Matrix (Fin n) (Fin n) ℝ)
    (U V : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (∑ l, entryPair (mixRectFamily R U l) (mixRectFamily R V l)) =
      ∑ a, ∑ b, (R.transpose * R) a b * entryPair (U a) (V b) := by
  simp only [entryPair_mix_two, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_comm

theorem directLinear_mix_direction (H : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin n) (Fin n) ℝ) (N : Fin n → Matrix (Fin n) (Fin n) ℝ) (l : Fin n) :
    directLinear H T (mixFamily R N l) = mixRectFamily R (fun a => directLinear H T (N a)) l := by
  ext i j
  simp only [directLinear, mixFamily, mixRectFamily, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

theorem direct_half_coefficient_whitening (H : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin n) (Fin n) ℝ) (N : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (∑ l, entryPair (mixFamily R N l) (directLinear H T (mixFamily R N l))) =
      ∑ a, ∑ b, (R.transpose * R) a b * entryPair (N a) (directLinear H T (N b)) := by
  simp only [directLinear_mix_direction]
  exact sum_entryPair_mix_two R N (fun a => directLinear H T (N a))

theorem rawGramDerivative_eq_direct_symmetrization (H : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (D : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    rawGramDerivative H T D i j = directLinear H T D i j + directLinear H T D j i := by
  have hc := Matrix.trace_mul_comm (T i * H) (T j * D)
  simp only [Matrix.mul_assoc] at hc
  change (T i * D * T j * H).trace + (T i * H * T j * D).trace = _
  rw [show (T i * H * T j * D).trace = (T j * D * T i * H).trace by
    simpa only [Matrix.mul_assoc] using hc]
  rfl

theorem pair_rawGramDerivative_eq_two_direct (H : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (C D : Matrix (Fin n) (Fin n) ℝ)
    (hC : C.IsSymm) :
    entryPair C (rawGramDerivative H T D) = 2 * entryPair C (directLinear H T D) := by
  have hs : (∑ i, ∑ j, C i j * directLinear H T D j i) =
      ∑ i, ∑ j, C i j * directLinear H T D i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hC.apply i j]
  simp only [entryPair, rawGramDerivative_eq_direct_symmetrization, mul_add,
    Finset.sum_add_distrib]
  rw [hs]
  ring

def directHalfEnergy (H : Matrix (Fin n) (Fin n) ℝ)
    (T N : Fin n → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ a, ∑ b, H⁻¹ a b * entryPair (N a) (directLinear H T (N b))

def directCrossEnergy (H : Matrix (Fin n) (Fin n) ℝ)
    (T N : Fin n → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ a, ∑ b, H⁻¹ a b * entryPair (N a) (rawGramDerivative H T (N b))

theorem directCrossEnergy_eq_twice_half (H : Matrix (Fin n) (Fin n) ℝ)
    (T N : Fin n → Matrix (Fin n) (Fin n) ℝ) (hN : ∀ a, (N a).IsSymm) :
    directCrossEnergy H T N = 2 * directHalfEnergy H T N := by
  simp only [directCrossEnergy, directHalfEnergy, pair_rawGramDerivative_eq_two_direct H T _ _ (hN _),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end KLSConstantImprovement.ActualDirectCubicCoefficients405

#print axioms KLSConstantImprovement.ActualDirectCubicCoefficients405.direct_half_coefficient_whitening
#print axioms KLSConstantImprovement.ActualDirectCubicCoefficients405.pair_rawGramDerivative_eq_two_direct
#print axioms KLSConstantImprovement.ActualDirectCubicCoefficients405.directCrossEnergy_eq_twice_half

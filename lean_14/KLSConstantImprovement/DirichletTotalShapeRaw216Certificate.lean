import Mathlib

/-! Unbuilt finite scalar nomination from positive-gap-recovery5.
This file proves polynomial and scalar implications only. Identifying
these coefficients with an original Dirichlet law remains in the paper
proof literature/positive-gap-recovery5-asymmetric-dirichlet-upper.md.
No arbitrary-law, product/image, kernel, or endpoint bridge is assumed.
The merger is the sole compiler and accepted-source owner. -/

noncomputable section
namespace KLSConstantImprovement.DirichletTotalShapeScalar

def denominator (s : ℝ) : ℝ := (s + 2) * (s + 3) * (s + 4) * (s + 5)
def sixthNumerator (s : ℝ) : ℝ := s ^ 2 * (s + 1) ^ 2
def kernelNumerator (s : ℝ) : ℝ := 4 * s ^ 3 - 14 * s ^ 2 - 114 * s - 120
def gapNumerator (s : ℝ) : ℝ := 4 * s * (s + 1) * (2 * s + 5)

theorem kernel_shift_identity (s : ℝ) :
    kernelNumerator s = 1340 + 806 * (s - 10) + 106 * (s - 10) ^ 2 +
      4 * (s - 10) ^ 3 := by
  unfold kernelNumerator
  ring

theorem raw216_shift_identity (s : ℝ) :
    6 * (denominator s - sixthNumerator s) * kernelNumerator s -
      gapNumerator s ^ 2 =
    45106400 + 75789920 * (s - 10) + 26745304 * (s - 10) ^ 2 +
      4176464 * (s - 10) ^ 3 + 335704 * (s - 10) ^ 4 +
      13664 * (s - 10) ^ 5 + 224 * (s - 10) ^ 6 := by
  unfold denominator sixthNumerator kernelNumerator gapNumerator
  ring

theorem kernel_numerator_pos {s : ℝ} (hs : 10 ≤ s) :
    0 < kernelNumerator s := by
  rw [kernel_shift_identity]
  have hx : 0 ≤ s - 10 := by linarith
  positivity

theorem raw216_numerator_pos {s : ℝ} (hs : 10 ≤ s) :
    0 < 6 * (denominator s - sixthNumerator s) * kernelNumerator s -
      gapNumerator s ^ 2 := by
  rw [raw216_shift_identity]
  have hx : 0 ≤ s - 10 := by linarith
  positivity

/-- A scalar transfer with the displayed variance-budget premise retained. -/
theorem raw216_of_completed_square_budget {N V g h k : ℝ}
    (hN : 0 ≤ N) (hk : 0 < k)
    (hgap : h * h ≤ 6 * (1 - g) * k)
    (hV : V ≤ (216 * g + 36 * h * h / k) * N) :
    V ≤ 216 * N := by
  have herr : 36 * h * h / k ≤ 216 * (1 - g) := by
    apply (div_le_iff₀ hk).2
    nlinarith [hgap]
  have hcap : 216 * g + 36 * h * h / k ≤ 216 := by linarith
  exact le_trans hV (mul_le_mul_of_nonneg_right hcap hN)

end KLSConstantImprovement.DirichletTotalShapeScalar
end

#print axioms KLSConstantImprovement.DirichletTotalShapeScalar.kernel_shift_identity
#print axioms KLSConstantImprovement.DirichletTotalShapeScalar.raw216_shift_identity
#print axioms KLSConstantImprovement.DirichletTotalShapeScalar.kernel_numerator_pos
#print axioms KLSConstantImprovement.DirichletTotalShapeScalar.raw216_numerator_pos
#print axioms KLSConstantImprovement.DirichletTotalShapeScalar.raw216_of_completed_square_budget

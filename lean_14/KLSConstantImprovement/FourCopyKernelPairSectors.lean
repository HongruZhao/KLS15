import KLSConstantImprovement.FourCopyKernelSixSquares

/-! The two trace-free sectors of a centered four-copy matrix, written using
opposite edge pairs.  The law-dependent comparison of their expected squares
is not asserted. -/
noncomputable section
open Matrix
namespace KLSConstantImprovement.FourCopyKernelPairSectors
open KLSConstantImprovement.FourCopyKernelSixSquares
set_option maxHeartbeats 3000000

def pairSumSquares (Q : FourMatrix) : ℝ :=
  ((Q 0 1 + Q 2 3) - (Q 0 2 + Q 1 3))^2 +
  ((Q 0 1 + Q 2 3) - (Q 0 3 + Q 1 2))^2 +
  ((Q 0 2 + Q 1 3) - (Q 0 3 + Q 1 2))^2

def pairDifferenceSquares (Q : FourMatrix) : ℝ :=
  (Q 2 3 - Q 0 1)^2 + (Q 1 3 - Q 0 2)^2 + (Q 1 2 - Q 0 3)^2

theorem pairSumSquares_nonneg (Q : FourMatrix) : 0 ≤ pairSumSquares Q := by
  unfold pairSumSquares
  positivity

theorem pairDifferenceSquares_nonneg (Q : FourMatrix) : 0 ≤ pairDifferenceSquares Q := by
  unfold pairDifferenceSquares
  positivity

private theorem diagonal_entries (Q : FourMatrix) (hQ : Q.IsSymm)
    (hrow : ∀ i, ∑ j, Q i j = 0) :
    Q 0 0 = -Q 0 1-Q 0 2-Q 0 3 ∧
    Q 1 1 = -Q 0 1-Q 1 2-Q 1 3 ∧
    Q 2 2 = -Q 0 2-Q 1 2-Q 2 3 ∧
    Q 3 3 = -Q 0 3-Q 1 3-Q 2 3 := by
  have h₀ := hrow 0
  have h₁ := hrow 1
  have h₂ := hrow 2
  have h₃ := hrow 3
  simp [Fin.sum_univ_succ, hQ.apply 0 1, hQ.apply 0 2, hQ.apply 0 3,
    hQ.apply 1 2, hQ.apply 1 3, hQ.apply 2 3] at h₀ h₁ h₂ h₃
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The six residuals form the two-dimensional opposite-pair sum sector. -/
theorem residualSquares_eq_pairSumSquares (Q : FourMatrix) (hQ : Q.IsSymm)
    (hrow : ∀ i, ∑ j, Q i j = 0) :
    residualSquares Q = pairSumSquares Q/6 := by
  obtain ⟨hd₀, hd₁, hd₂, hd₃⟩ := diagonal_entries Q hQ hrow
  simp [residualSquares, FourCopyKernelSixSquares.residual, pairSumSquares, Matrix.trace, Fin.sum_univ_succ,
    hd₀, hd₁, hd₂, hd₃]
  ring

/-- The trace-free square splits into its two and three dimensional sectors. -/
theorem traceFreeSquare_eq_pairSectors (Q : FourMatrix) (hQ : Q.IsSymm)
    (hrow : ∀ i, ∑ j, Q i j = 0) :
    traceFreeSquare Q = pairSumSquares Q/3 + 2*pairDifferenceSquares Q := by
  obtain ⟨hd₀, hd₁, hd₂, hd₃⟩ := diagonal_entries Q hQ hrow
  simp [traceFreeSquare, pairSumSquares, pairDifferenceSquares, Matrix.trace,
    Matrix.mul_apply, Fin.sum_univ_succ, hQ.apply 0 1, hQ.apply 0 2,
    hQ.apply 0 3, hQ.apply 1 2, hQ.apply 1 3, hQ.apply 2 3,
    hd₀, hd₁, hd₂, hd₃]
  ring

theorem traceFreeSquare_nonneg (Q : FourMatrix) (hQ : Q.IsSymm)
    (hrow : ∀ i, ∑ j, Q i j = 0) : 0 ≤ traceFreeSquare Q := by
  rw [traceFreeSquare_eq_pairSectors Q hQ hrow]
  exact add_nonneg (div_nonneg (pairSumSquares_nonneg Q) (by norm_num))
    (mul_nonneg (by norm_num) (pairDifferenceSquares_nonneg Q))

/-- The kernel is a comparison of squares in different permutation sectors. -/
theorem kernel_eq_pairSectors (Q : FourMatrix) (hQ : Q.IsSymm)
    (hrow : ∀ i, ∑ j, Q i j = 0) :
    kernel Q = (5/6 : ℝ)*pairSumSquares Q - (4/3 : ℝ)*pairDifferenceSquares Q := by
  rw [kernel_decomposition Q hQ hrow, residualSquares_eq_pairSumSquares Q hQ hrow,
    traceFreeSquare_eq_pairSectors Q hQ hrow]
  ring

/-- Exact scalar conversion after integration; it does not assert the comparison. -/
theorem sector_comparison_iff {p o k d : ℝ}
    (hdecomp : k = (5/6 : ℝ)*p - (4/3 : ℝ)*o) :
    (-(57/2 : ℝ)*d ≤ k) ↔ o ≤ (5/8 : ℝ)*p + (171/8 : ℝ)*d := by
  constructor <;> intro h <;> linarith

theorem centered_exponential_sector_balance :
    (48 : ℝ) = 288/6 ∧ (456 : ℝ) = 288/3 + 2*180 ∧
    (180 : ℝ) = (5/8)*288 := by norm_num

end KLSConstantImprovement.FourCopyKernelPairSectors

#print axioms KLSConstantImprovement.FourCopyKernelPairSectors.pairSumSquares_nonneg
#print axioms KLSConstantImprovement.FourCopyKernelPairSectors.pairDifferenceSquares_nonneg
#print axioms KLSConstantImprovement.FourCopyKernelPairSectors.residualSquares_eq_pairSumSquares
#print axioms KLSConstantImprovement.FourCopyKernelPairSectors.traceFreeSquare_eq_pairSectors
#print axioms KLSConstantImprovement.FourCopyKernelPairSectors.traceFreeSquare_nonneg
#print axioms KLSConstantImprovement.FourCopyKernelPairSectors.kernel_eq_pairSectors
#print axioms KLSConstantImprovement.FourCopyKernelPairSectors.sector_comparison_iff
#print axioms KLSConstantImprovement.FourCopyKernelPairSectors.centered_exponential_sector_balance

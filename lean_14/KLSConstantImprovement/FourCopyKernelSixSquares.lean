import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-! Exact finite-dimensional algebra for the centered four-copy kernel.
These identities preserve the positive residual squares.  No integrated
curvature inequality or new universal Poincare bound is assumed or proved. -/
noncomputable section
open Matrix
namespace KLSConstantImprovement.FourCopyKernelSixSquares
set_option maxHeartbeats 3000000

abbrev FourMatrix := Matrix (Fin 4) (Fin 4) ℝ

def diagonalSquares (Q : FourMatrix) : ℝ := ∑ i, (Q i i)^2

def residual (Q : FourMatrix) (i j : Fin 4) : ℝ :=
  Q i j + (Q i i + Q j j)/2 - Matrix.trace Q/6

def residualSquares (Q : FourMatrix) : ℝ :=
  (residual Q 0 1)^2 + (residual Q 0 2)^2 + (residual Q 0 3)^2 +
  (residual Q 1 2)^2 + (residual Q 1 3)^2 + (residual Q 2 3)^2

def traceFreeSquare (Q : FourMatrix) : ℝ :=
  Matrix.trace (Q * Q) - (Matrix.trace Q)^2/3

def kernel (Q : FourMatrix) : ℝ :=
  (5/2 : ℝ)*Matrix.trace (Q * Q) + (3/4 : ℝ)*(Matrix.trace Q)^2 -
    (19/3 : ℝ)*diagonalSquares Q

/-- The scalar identity before specializing to a centered symmetric matrix. -/
theorem coordinate_six_squares
    {d₀ d₁ d₂ d₃ a b c e f g : ℝ}
    (h₀ : d₀ + a + b + c = 0) (h₁ : a + d₁ + e + f = 0)
    (h₂ : b + e + d₂ + g = 0) (h₃ : c + f + g + d₃ = 0) :
    (a + (d₀+d₁)/2 - (d₀+d₁+d₂+d₃)/6)^2 +
    (b + (d₀+d₂)/2 - (d₀+d₁+d₂+d₃)/6)^2 +
    (c + (d₀+d₃)/2 - (d₀+d₁+d₂+d₃)/6)^2 +
    (e + (d₁+d₂)/2 - (d₀+d₁+d₂+d₃)/6)^2 +
    (f + (d₁+d₃)/2 - (d₀+d₁+d₂+d₃)/6)^2 +
    (g + (d₂+d₃)/2 - (d₀+d₁+d₂+d₃)/6)^2 =
      (1/2 : ℝ)*(d₀^2+d₁^2+d₂^2+d₃^2 + 2*(a^2+b^2+c^2+e^2+f^2+g^2)) +
      (d₀+d₁+d₂+d₃)^2/12 - (d₀^2+d₁^2+d₂^2+d₃^2) := by
  linear_combination (d₀-(d₀+d₁+d₂+d₃)/6)*h₀ +
    (d₁-(d₀+d₁+d₂+d₃)/6)*h₁ +
    (d₂-(d₀+d₁+d₂+d₃)/6)*h₂ +
    (d₃-(d₀+d₁+d₂+d₃)/6)*h₃

theorem residualSquares_nonneg (Q : FourMatrix) : 0 ≤ residualSquares Q := by
  unfold residualSquares
  positivity

/-- The six residual squares exactly measure the diagonal inequality. -/
theorem six_squares_identity (Q : FourMatrix) (hQ : Q.IsSymm)
    (hrow : ∀ i, ∑ j, Q i j = 0) :
    residualSquares Q = (1/2 : ℝ)*Matrix.trace (Q*Q) +
      (Matrix.trace Q)^2/12 - diagonalSquares Q := by
  have h₀ := hrow 0
  have h₁ := hrow 1
  have h₂ := hrow 2
  have h₃ := hrow 3
  simp [Fin.sum_univ_succ] at h₀ h₁ h₂ h₃
  have hs₁₀ := hQ.apply 0 1
  have hs₂₀ := hQ.apply 0 2
  have hs₃₀ := hQ.apply 0 3
  have hs₂₁ := hQ.apply 1 2
  have hs₃₁ := hQ.apply 1 3
  have hs₃₂ := hQ.apply 2 3
  have hh := coordinate_six_squares (d₀ := Q 0 0) (d₁ := Q 1 1)
    (d₂ := Q 2 2) (d₃ := Q 3 3) (a := Q 0 1) (b := Q 0 2) (c := Q 0 3)
    (e := Q 1 2) (f := Q 1 3) (g := Q 2 3)
    (by simpa [add_assoc] using h₀)
    (by simpa [hs₁₀, add_assoc] using h₁)
    (by simpa [hs₂₀, hs₂₁, add_assoc] using h₂)
    (by simpa [hs₃₀, hs₃₁, hs₃₂, add_assoc] using h₃)
  simp [residualSquares, residual, diagonalSquares, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_succ, hs₁₀, hs₂₀, hs₃₀, hs₂₁, hs₃₁, hs₃₂] at hh ⊢
  nlinarith only [hh]

theorem diagonalSquares_le (Q : FourMatrix) (hQ : Q.IsSymm)
    (hrow : ∀ i, ∑ j, Q i j = 0) :
    diagonalSquares Q ≤ (1/2 : ℝ)*Matrix.trace (Q*Q) + (Matrix.trace Q)^2/12 := by
  have hid := six_squares_identity Q hQ hrow
  have hpos := residualSquares_nonneg Q
  linarith

/-- The pointwise decomposition keeps both terms needed by the global estimate. -/
theorem kernel_decomposition (Q : FourMatrix) (hQ : Q.IsSymm)
    (hrow : ∀ i, ∑ j, Q i j = 0) :
    kernel Q = (19/3 : ℝ)*residualSquares Q - (2/3 : ℝ)*traceFreeSquare Q := by
  rw [six_squares_identity Q hQ hrow]
  unfold kernel traceFreeSquare
  ring

theorem kernel_lower (Q : FourMatrix) (hQ : Q.IsSymm)
    (hrow : ∀ i, ∑ j, Q i j = 0) :
    -(2/3 : ℝ)*traceFreeSquare Q ≤ kernel Q := by
  rw [kernel_decomposition Q hQ hrow]
  have hpos := residualSquares_nonneg Q
  linarith

/-- Scalar form usable after integration: positive-square cancellation is retained. -/
theorem integrated_balance_iff {a r k d : ℝ}
    (hdecomp : k = (19/3 : ℝ)*r - (2/3 : ℝ)*a) :
    (-(57/2 : ℝ)*d ≤ k) ↔ a ≤ (19/2 : ℝ)*r + (171/4 : ℝ)*d := by
  constructor <;> intro h <;> linarith

/-- The curvature convention differs from the four-copy kernel by four deficits. -/
theorem curvature_balance_iff {a r k j d : ℝ}
    (hdecomp : k = (19/3 : ℝ)*r - (2/3 : ℝ)*a) (hcurv : j = k - 4*d) :
    (-(65/2 : ℝ)*d ≤ j) ↔ a ≤ (19/2 : ℝ)*r + (171/4 : ℝ)*d := by
  constructor <;> intro h <;> linarith

/-- Exact numerical equality for the separately proved centered-exponential moments. -/
theorem centered_exponential_balance :
    (19/3 : ℝ)*48 = 304 ∧ (2/3 : ℝ)*456 = 304 ∧
    (19/3 : ℝ)*48 - (2/3 : ℝ)*456 = 0 := by norm_num

end KLSConstantImprovement.FourCopyKernelSixSquares

#print axioms KLSConstantImprovement.FourCopyKernelSixSquares.coordinate_six_squares
#print axioms KLSConstantImprovement.FourCopyKernelSixSquares.residualSquares_nonneg
#print axioms KLSConstantImprovement.FourCopyKernelSixSquares.six_squares_identity
#print axioms KLSConstantImprovement.FourCopyKernelSixSquares.diagonalSquares_le
#print axioms KLSConstantImprovement.FourCopyKernelSixSquares.kernel_decomposition
#print axioms KLSConstantImprovement.FourCopyKernelSixSquares.kernel_lower
#print axioms KLSConstantImprovement.FourCopyKernelSixSquares.integrated_balance_iff
#print axioms KLSConstantImprovement.FourCopyKernelSixSquares.curvature_balance_iff
#print axioms KLSConstantImprovement.FourCopyKernelSixSquares.centered_exponential_balance

import Mathlib

/-!
Finite Gram bindings and integrated/scalar consequences of the new full
tensor lift. The right-weighted three-lines proof is in
literature/original-upper-recovery6-all-tensor-third-sandwich.md.

The pointwise tensor lift, the original same-joint-H third sandwich, and
the regular source-PDE affine trace identity are explicit inputs here.
This module does not assert the universal combined Poisson budget.
-/
noncomputable section
open Finset MeasureTheory

namespace KLSConstantImprovement.OriginalUpperRecovery6TensorGram

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def tensorNormSq (T : ι → ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, T i j k ^ 2

def sliceGram (T : ι → ι → ι → ℝ) (i j : ι) : ℝ :=
  ∑ a, ∑ b, T i a b * T j a b

def matrixTrace (A : Matrix ι ι ℝ) : ℝ := ∑ i, A i i

def matrixCubeTrace (A : Matrix ι ι ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, A i j * A j k * A k i

def tensorThird (T : ι → ι → ι → ℝ) (H : Matrix ι ι ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
    T i j k * H i a * H j b * H k c * T a b c

theorem tensorNormSq_nonneg (T : ι → ι → ι → ℝ) :
    0 ≤ tensorNormSq T := by
  unfold tensorNormSq
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun k _ => sq_nonneg (T i j k)

theorem sliceGram_symmetric (T : ι → ι → ι → ℝ) (i j : ι) :
    sliceGram T i j = sliceGram T j i := by
  unfold sliceGram
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact mul_comm _ _

theorem trace_sliceGram (T : ι → ι → ι → ℝ) :
    matrixTrace (sliceGram T) = tensorNormSq T := by
  simp only [matrixTrace, sliceGram, tensorNormSq, pow_two]

/-- Full symmetry identifies the same Gram with the sum of slice squares.
The two symmetries are finite tensor inputs, not a diagonalization. -/
theorem sliceGram_eq_sum_sliceSquares (T : ι → ι → ι → ℝ)
    (hfirst : ∀ i a b, T i a b = T a i b)
    (hlast : ∀ a i b, T a i b = T a b i) (i j : ι) :
    sliceGram T i j = ∑ a, ∑ b, T a i b * T a b j := by
  unfold sliceGram
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [hfirst i a b, hfirst j a b, hlast a j b]

/-- Integrate the pointwise full tensor lift against the SAME original
joint kernel law. The sandwich and trace-cube binding are explicit. -/
theorem integrated_tensor_third_sandwich {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : ι → ι → ι → ℝ) (B : Matrix ι ι ℝ)
    (H : Ω → Matrix ι ι ℝ)
    (hT : Integrable (fun ω => tensorThird T (H ω)) μ)
    (hM : Integrable (fun ω => matrixCubeTrace (B * H ω)) μ)
    (hpoint : ∀ᵐ ω ∂μ,
      tensorThird T (H ω) ≤ matrixCubeTrace (B * H ω))
    (htrace : matrixCubeTrace B = tensorNormSq T)
    (hsandwich : (∫ ω, matrixCubeTrace (B * H ω) ∂μ) ≤
      (8 * Real.sqrt 2) * matrixCubeTrace B) :
    (∫ ω, tensorThird T (H ω) ∂μ) ≤
      (8 * Real.sqrt 2) * tensorNormSq T := by
  have hi := integral_mono_ae hT hM hpoint
  rw [htrace] at hsandwich
  exact hi.trans hsandwich

theorem tensor_third_square_bound {W N : ℝ}
    (hW : 0 ≤ W) (hN : 0 ≤ N)
    (hbound : W ≤ (8 * Real.sqrt 2) * N) :
    W ^ 2 ≤ 128 * N ^ 2 := by
  have hroot : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsum : 0 ≤ (8 * Real.sqrt 2) * N + W := by positivity
  have hp := mul_nonneg (sub_nonneg.mpr hbound) hsum
  have heq : ((8 * Real.sqrt 2) * N) ^ 2 = 128 * N ^ 2 := by
    rw [mul_pow, mul_pow, hsq]
    ring
  nlinarith [heq]

/-- The source connection/curvature charge keeps its sign and gives an
all-tensor numerical affine trace component. It does not pay a commutator
or identify this p with the ordinary target Poisson curvature. -/
theorem affine_trace_bound_from_tensor_third {W N J b p : ℝ}
    (hW : 0 ≤ W) (hN : 0 ≤ N) (hp : 0 ≤ p)
    (hbound : W ≤ (8 * Real.sqrt 2) * N)
    (hidentity : J = W + 2*b)
    (hcharge : 2 * b ^ 2 ≤ W * (W-p)) :
    J ≤ (16 + 8 * Real.sqrt 2) * N := by
  have hWsq := tensor_third_square_bound hW hN hbound
  have hbSq : b ^ 2 ≤ 64 * N ^ 2 := by
    nlinarith [mul_nonneg hW hp]
  have hb : b ≤ 8*N := by
    by_contra h
    have hlt : 8*N < b := lt_of_not_ge h
    have hsum : 0 < b+8*N := by linarith
    have hprod := mul_pos (sub_pos.mpr hlt) hsum
    nlinarith
  nlinarith

end KLSConstantImprovement.OriginalUpperRecovery6TensorGram

#print axioms KLSConstantImprovement.OriginalUpperRecovery6TensorGram.tensorNormSq_nonneg
#print axioms KLSConstantImprovement.OriginalUpperRecovery6TensorGram.sliceGram_symmetric
#print axioms KLSConstantImprovement.OriginalUpperRecovery6TensorGram.trace_sliceGram
#print axioms KLSConstantImprovement.OriginalUpperRecovery6TensorGram.sliceGram_eq_sum_sliceSquares
#print axioms KLSConstantImprovement.OriginalUpperRecovery6TensorGram.integrated_tensor_third_sandwich
#print axioms KLSConstantImprovement.OriginalUpperRecovery6TensorGram.tensor_third_square_bound
#print axioms KLSConstantImprovement.OriginalUpperRecovery6TensorGram.affine_trace_bound_from_tensor_third

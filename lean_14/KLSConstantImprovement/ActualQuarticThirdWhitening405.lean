import KLSConstantImprovement.ActualQuarticCongruence405
import KLSConstantImprovement.ActualFullTensorWhitening

/-! All three source-tensor indices are whitened by the same matrix.
Full third symmetry gives the literal slice-square curvature identity;
the separate quartic row family is absent from this construction. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualQuarticThirdWhitening405
open ActualQuarticWhiteFrame405 ActualQuarticCongruence405 ActualFullTensorWhitening
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
set_option maxHeartbeats 1500000

def mixFamily (R : Matrix ι ι ℝ) (N : ι → Matrix ι ι ℝ) : ι → Matrix ι ι ℝ :=
  fun l => ∑ a, R l a • N a

def whiteThirdSlice (R : Matrix ι ι ℝ) (N : ι → Matrix ι ι ℝ) : ι → Matrix ι ι ℝ :=
  fun l => R * mixFamily R N l * R

theorem whiteThirdSlice_eq_mix (R : Matrix ι ι ℝ) (N : ι → Matrix ι ι ℝ) :
    whiteThirdSlice R N = mixFamily R (rowWhitening R N) := by
  funext l
  simp only [whiteThirdSlice, mixFamily, rowWhitening, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul]

theorem whiteThirdSlice_symmetric (R : Matrix ι ι ℝ) (hR : R.IsSymm)
    (N : ι → Matrix ι ι ℝ) (hN : ∀ a, (N a).IsSymm) (l : ι) :
    (whiteThirdSlice R N l).IsSymm := by
  change (R * (∑ a, R l a • N a) * R).transpose = R * (∑ a, R l a • N a) * R
  simp only [Matrix.transpose_mul, Matrix.transpose_sum, Matrix.transpose_smul, hR.eq]
  simp only [(hN _).eq, Matrix.mul_assoc]

theorem whiteThirdSlice_eq_threeSlot (R : Matrix ι ι ℝ) (hR : R.IsSymm)
    (N : ι → Matrix ι ι ℝ) (l i j : ι) :
    whiteThirdSlice R N l i j = threeSlotAction R N l i j := by
  rw [whiteThirdSlice_eq_mix]
  simp only [mixFamily, rowWhitening, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, threeSlotAction]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [hR.apply j c]
  ring

theorem whiteThirdSlice_cyclic (R : Matrix ι ι ℝ) (hR : R.IsSymm)
    (N : ι → Matrix ι ι ℝ) (hN : ∀ i j k, N i j k = N j k i) (i j k : ι) :
    whiteThirdSlice R N i j k = whiteThirdSlice R N j k i := by
  rw [whiteThirdSlice_eq_threeSlot R hR, whiteThirdSlice_eq_threeSlot R hR]
  exact threeSlotAction_preserves_cyclic R N hN i j k

theorem full_symmetric_slice_square (N : ι → Matrix ι ι ℝ)
    (hN12 : ∀ i j k, N i j k = N j i k)
    (hN23 : ∀ i j k, N i j k = N i k j) :
    (∑ l, N l * N l) = whiteGram N := by
  ext i j
  simp only [whiteGram, Matrix.sum_apply, Matrix.mul_apply, Matrix.trace, Matrix.diag]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro a _
  have hs : N k a j = N j a k := by
    rw [hN23 k a j, hN12 k j a, hN23 j k a]
  rw [hN12 k i a, hs]

theorem whiteGram_mixFamily (R : Matrix ι ι ℝ) (N : ι → Matrix ι ι ℝ) :
    whiteGram (mixFamily R N) = R * whiteGram N * R.transpose := by
  ext i j
  simp only [whiteGram, mixFamily, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem white_third_slice_square (R : Matrix ι ι ℝ) (hR : R.IsSymm)
    (N : ι → Matrix ι ι ℝ)
    (hN12 : ∀ i j k, N i j k = N j i k)
    (hN23 : ∀ i j k, N i j k = N i k j) :
    (∑ l, whiteThirdSlice R N l * whiteThirdSlice R N l) =
      R * rawGram (R * R) N * R := by
  have hNs (a : ι) : (N a).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    exact hN23 a j i
  have hMs := whiteThirdSlice_symmetric R hR N hNs
  have hMc : ∀ i j k, whiteThirdSlice R N i j k = whiteThirdSlice R N j k i := by
    apply whiteThirdSlice_cyclic R hR N
    intro i j k
    exact (hN12 i j k).trans (hN23 j i k)
  have hM12 : ∀ i j k, whiteThirdSlice R N i j k = whiteThirdSlice R N j i k := by
    intro i j k
    exact (hMc i j k).trans ((hMs j).apply i k)
  have hM23 : ∀ i j k, whiteThirdSlice R N i j k = whiteThirdSlice R N i k j := by
    intro i j k
    exact (hMs i).apply k j
  rw [full_symmetric_slice_square _ hM12 hM23, whiteThirdSlice_eq_mix,
    whiteGram_mixFamily, ← rawGram_eq_white R N, hR.eq]

theorem unwhiten_whiteThirdSlice (Q R : Matrix ι ι ℝ) (hQR : Q * R = 1)
    (hRQ : R * Q = 1) (N : ι → Matrix ι ι ℝ) (l : ι) :
    Q * whiteThirdSlice R N l * Q = mixFamily R N l := by
  calc
    _ = (Q * R) * mixFamily R N l * (R * Q) := by
      simp only [whiteThirdSlice, Matrix.mul_assoc]
    _ = _ := by rw [hQR, hRQ, Matrix.one_mul, Matrix.mul_one]

theorem unwhiten_slice_square_curvature (Q R : Matrix ι ι ℝ)
    (hQR : Q * R = 1) (hRQ : R * Q = 1) (hR : R.IsSymm)
    (N : ι → Matrix ι ι ℝ)
    (hN12 : ∀ i j k, N i j k = N j i k)
    (hN23 : ∀ i j k, N i j k = N i k j) :
    Q * (∑ l, whiteThirdSlice R N l * whiteThirdSlice R N l) * Q =
      rawGram (R * R) N := by
  rw [white_third_slice_square R hR N hN12 hN23]
  calc
    _ = (Q * R) * rawGram (R * R) N * (R * Q) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hQR, hRQ, Matrix.one_mul, Matrix.mul_one]

end KLSConstantImprovement.ActualQuarticThirdWhitening405

#print axioms KLSConstantImprovement.ActualQuarticThirdWhitening405.whiteThirdSlice_eq_threeSlot
#print axioms KLSConstantImprovement.ActualQuarticThirdWhitening405.whiteThirdSlice_symmetric
#print axioms KLSConstantImprovement.ActualQuarticThirdWhitening405.white_third_slice_square
#print axioms KLSConstantImprovement.ActualQuarticThirdWhitening405.unwhiten_slice_square_curvature

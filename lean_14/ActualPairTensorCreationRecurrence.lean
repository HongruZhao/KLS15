import ActualPairTensorCreation
import PairTensorAnnihilation
import PairTensorDisjointFrame
import PairTensorDisjointAlgebra

/-! The actual all-rank cubic creation/annihilation bounds. All tensors
are ordered Hilbert--Schmidt tensors; the input is fully symmetric. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext
open KLSBelow25.PairTensor KLSBelow25.PairProjection
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

private theorem creation_cap_div_choose (r : ℕ) :
    (((r : ℝ)+3)^2*((r : ℝ)+2)*((r : ℝ)+3-1/3))/
      (Nat.choose (r+3) 2 : ℝ)^2 = 4+8/(3*((r : ℝ)+2)) := by
  rw [Nat.cast_choose_two]
  convert next_annihilation_cap (N:=r+3) (by omega) using 1 <;> push_cast <;> ring

/-- Genuine all-rank creation norm, with the literal unordered-pair sum. -/
theorem actual_pair_creation_square_le {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (r : ℕ) (T : Tensor (ι := Fin n) (r+2)) (hT : Symmetric T) :
    square (creation (actualThirdCubicArray μ) T) ≤
      ((r : ℝ)+3)^2*((r : ℝ)+2)*((r : ℝ)+3-1/3)*square T := by
  induction r with
  | zero =>
    norm_num
    exact actual_pair_creation_three_square_le hμ T hT
  | succ r ih =>
    let B := ((r : ℝ)+3)^2*((r : ℝ)+2)*((r : ℝ)+3-1/3)
    have hB : 0≤B := by
      have hr : 0≤(r : ℝ) := Nat.cast_nonneg _
      have hf : 0≤(r : ℝ)+3-1/3 := by linarith
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (by positivity)) hf
    have hC : ∀ H : Tensor (ι := Fin n) (r+2),Symmetric H →
        square (creation (actualThirdCubicArray μ) H)≤B*square H := by
      intro H hH
      exact ih H hH
    have he := annihilation_exchange_le (actualThirdCubicArray μ) T hT B hB hC
    have hs : pairing
        (kernel (actualThirdCubicArray μ) T (incidentPair (0 : Fin (r+3))))
        (kernel (actualThirdCubicArray μ) T (disjointPair r)) ≤
          (4+8/(3*((r : ℝ)+2)))*square T := by
      rw [kernel_disjoint_pairing_eq (actualThirdCubicArray μ) (actualThirdCumulant_swap_first μ) T hT,
        coordinate_disjoint_trace (actualThirdCubicArray μ) T hT]
      simpa only [B,creation_cap_div_choose] using he
    have hb := actual_pair_creation_square_le_of_disjoint hμ T hT hs
    convert hb using 1
    push_cast
    ring

/-- The actual trace channel of the raw annihilation tensor, with no
surrogate covariance or assumed lower Gram bound. -/
theorem actual_pair_annihilation_exchange_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {r : ℕ} (T : Tensor (ι := Fin n) (r+3))
    (hT : Symmetric T) :
    exchange (annihilation (actualThirdCubicArray μ) T) ≤
      (4+8/(3*((r : ℝ)+2)))*square T := by
  let B := ((r : ℝ)+3)^2*((r : ℝ)+2)*((r : ℝ)+3-1/3)
  have hB : 0≤B := by
    have hr : 0≤(r : ℝ) := Nat.cast_nonneg _
    have hf : 0≤(r : ℝ)+3-1/3 := by linarith
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (by positivity)) hf
  have he := annihilation_exchange_le (actualThirdCubicArray μ) T hT B hB
    (fun H hH => actual_pair_creation_square_le hμ r H hH)
  simpa only [B,creation_cap_div_choose] using he

/-- The exact disjoint pair contraction bound needed by the actual
all-degree covariance-noise identity. -/
theorem actual_pair_disjoint_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {r : ℕ} (T : Tensor (ι := Fin n) (r+3))
    (hT : Symmetric T) :
    pairing (kernel (actualThirdCubicArray μ) T (incidentPair (0 : Fin (r+3))))
      (kernel (actualThirdCubicArray μ) T (disjointPair r)) ≤
        (4+8/(3*((r : ℝ)+2)))*square T := by
  rw [kernel_disjoint_pairing_eq (actualThirdCubicArray μ) (actualThirdCumulant_swap_first μ) T hT,
    coordinate_disjoint_trace (actualThirdCubicArray μ) T hT]
  exact actual_pair_annihilation_exchange_le hμ T hT

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actual_pair_creation_square_le
#print axioms KLS.DeterministicBridgeIntegration.actual_pair_annihilation_exchange_le
#print axioms KLS.DeterministicBridgeIntegration.actual_pair_disjoint_le

import PairTensorRepresentatives
import ActualPairTensorSlotBounds
import PairProjectionCreationBound

/-! The actual creation base estimate and its exact next-grade reduction.
The only input to the latter is the lower-grade disjoint contraction, which
is supplied by creation/annihilation duality in the recursive theorem. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext
open KLSBelow25.PairTensor KLSBelow25.PairProjection
variable {n r : ℕ}
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem actual_pair_creation_three_square_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Tensor (ι := Fin n) 2) (hT : Symmetric T) :
    square (creation (actualThirdCubicArray μ) T) ≤ 48*square T := by
  let U := fun e : Pair 3 => toHilbert (kernel (actualThirdCubicArray μ) T e)
  have hg := kernel_gram_of_no_disjoint (actualThirdCubicArray μ)
    (actualThirdCumulant_swap_first μ) T hT
    (incidentPair (0 : Fin 2)) (incidentPair (1 : Fin 2))
    (incident_intersection_card _ _ (by decide)) pairs_three_intersect
  have hq : pairing (kernel (actualThirdCubicArray μ) T (incidentPair 0))
      (kernel (actualThirdCubicArray μ) T (incidentPair 0)) ≤ 8*square T := by
    simpa only [pairing,square,pow_two] using actual_pair_kernel_square_le_eight hμ T hT 0
  have hr := actual_pair_kernel_cross_le_four hμ T hT (0 : Fin 2) 1 (by decide)
  have hs : (0 : ℝ)≤(4+8/(3*((3 : ℝ)-2)))*square T := by
    have hh := square_nonneg T
    norm_num
  have hb := sumPairs_sq_le_closed U hg (by omega : 3≤3) hq hr hs
  rw [pair_sum_toHilbert,toHilbert_norm_sq] at hb
  norm_num at hb
  exact hb

theorem actual_pair_creation_square_le_of_disjoint {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Tensor (ι := Fin n) (r+3)) (hT : Symmetric T)
    (hs : pairing (kernel (actualThirdCubicArray μ) T (incidentPair (0 : Fin (r+3))))
      (kernel (actualThirdCubicArray μ) T (disjointPair r)) ≤
        (4+8/(3*((r : ℝ)+2)))*square T) :
    square (creation (actualThirdCubicArray μ) T) ≤
      ((r : ℝ)+4)^2*((r : ℝ)+3)*((r : ℝ)+4-1/3)*square T := by
  let U := fun e : Pair (r+4) => toHilbert (kernel (actualThirdCubicArray μ) T e)
  have hg := kernel_gram_of_representatives (actualThirdCubicArray μ)
    (actualThirdCumulant_swap_first μ) T hT
    (incidentPair (0 : Fin (r+3))) (incidentPair (1 : Fin (r+3))) (disjointPair r)
    (incident_intersection_card _ _ (by norm_num [Fin.ext_iff])) disjoint_intersection_card
  have hq : pairing (kernel (actualThirdCubicArray μ) T (incidentPair 0))
      (kernel (actualThirdCubicArray μ) T (incidentPair 0)) ≤ 8*square T := by
    simpa only [pairing,square,pow_two] using actual_pair_kernel_square_le_eight hμ T hT 0
  have hr := actual_pair_kernel_cross_le_four hμ T hT (0 : Fin (r+3)) 1
    (by norm_num [Fin.ext_iff])
  have hs' : pairing (kernel (actualThirdCubicArray μ) T (incidentPair 0))
      (kernel (actualThirdCubicArray μ) T (disjointPair r)) ≤
        (4+8/(3*(((r+4 : ℕ) : ℝ)-2)))*square T := by
    convert hs using 1
    push_cast
    ring
  have hb := sumPairs_sq_le_closed U hg (by omega : 3≤r+4) hq hr hs'
  rw [pair_sum_toHilbert,toHilbert_norm_sq] at hb
  convert hb using 1
  push_cast
  ring

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actual_pair_creation_three_square_le
#print axioms KLS.DeterministicBridgeIntegration.actual_pair_creation_square_le_of_disjoint

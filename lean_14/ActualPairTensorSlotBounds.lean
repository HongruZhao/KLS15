import PairTensorCoordinateSlots
import ActualCubicCreationBound
import ActualPairTensorSymmetry

/-! Actual one-slot eight and distinct-slot four for the literal pair
insertion kernel, on arbitrary symmetric tensors under an admissible law. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLSBelow25.PairTensor
variable {ι : Type*} [Fintype ι] {r : ℕ}

theorem sum_tensor_cons (F : (Fin (r+2)→ι)→ℝ) :
    (∑ a,F a)=∑ i : ι,∑ a : Fin (r+1)→ι,F (Fin.cons i a) := by
  exact sum_cons_coordinates F

end KLSBelow25.PairTensor
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLS.TensorEnergy
open KLSBelow25.PairTensor
variable {n r : ℕ}
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem actual_pair_kernel_cons (μ : Measure (Space n))
    (T : Tensor (ι := Fin n) (r+1)) (hT : Symmetric T)
    (s : Fin (r+1)) (i : Fin n) (a : Fin (r+1)→Fin n) :
    kernel (actualThirdCubicArray μ) T (incidentPair s) (Fin.cons i a)=
      coordinateSlot s (thirdCumulantMatrix μ (MomentMap.coordinateVector i)) T a := by
  exact kernel_incidentPair_cons _ (actualThirdCumulant_swap_first μ) T hT s i a

theorem actual_pair_kernel_square_le_eight {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Tensor (ι := Fin n) (r+1))
    (hT : Symmetric T) (s : Fin (r+1)) :
    square (kernel (actualThirdCubicArray μ) T (incidentPair s))≤8*square T := by
  have hh := thirdCumulant_tensor_single_slot_le_eight hμ s T
  simp only [←coordinateSlot_eq_tensorSlot,dotProduct,←pow_two] at hh
  simpa only [square,sum_tensor_cons,actual_pair_kernel_cons μ T hT] using hh

theorem actual_pair_kernel_cross_le_four {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Tensor (ι := Fin n) (r+1))
    (hT : Symmetric T) (s t : Fin (r+1)) (hst : s≠t) :
    pairing (kernel (actualThirdCubicArray μ) T (incidentPair s))
      (kernel (actualThirdCubicArray μ) T (incidentPair t))≤4*square T := by
  have hTc : CoordinateTensorSymmetric T := fun s t a => hT (Equiv.swap s t) a
  have hh := thirdCumulant_distinct_slot_pairing_le_four hμ hTc hst
  simpa only [pairing,square,sum_tensor_cons,actual_pair_kernel_cons μ T hT] using hh

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actual_pair_kernel_square_le_eight
#print axioms KLS.DeterministicBridgeIntegration.actual_pair_kernel_cross_le_four

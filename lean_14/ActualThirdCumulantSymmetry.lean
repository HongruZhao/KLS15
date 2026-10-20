import UniversalTwoSlot

/-! Literal full permutation symmetry of the actual coordinate third moment.
No regularity or surrogate tensor is assumed. -/
noncomputable section
open MeasureTheory
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration
variable {n : ℕ}

theorem actualThirdCumulant_swap_first (μ : Measure (Space n)) (i a b : Fin n) :
    thirdCumulantMatrix μ (MomentMap.coordinateVector i) a b =
      thirdCumulantMatrix μ (MomentMap.coordinateVector a) i b := by
  rw [thirdCumulantMatrix_coordinate_eq_cubic,
    thirdCumulantMatrix_coordinate_eq_cubic]
  apply integral_congr_ae
  exact .of_forall fun x => by ring

theorem actualThirdCumulant_swap_last (μ : Measure (Space n)) (i a b : Fin n) :
    thirdCumulantMatrix μ (MomentMap.coordinateVector i) a b =
      thirdCumulantMatrix μ (MomentMap.coordinateVector i) b a := by
  rw [thirdCumulantMatrix_coordinate_eq_cubic,
    thirdCumulantMatrix_coordinate_eq_cubic]
  apply integral_congr_ae
  exact .of_forall fun x => by ring

theorem actualThirdCumulant_cyclic (μ : Measure (Space n)) (i a b : Fin n) :
    thirdCumulantMatrix μ (MomentMap.coordinateVector i) a b =
      thirdCumulantMatrix μ (MomentMap.coordinateVector b) i a := by
  rw [thirdCumulantMatrix_coordinate_eq_cubic,
    thirdCumulantMatrix_coordinate_eq_cubic]
  apply integral_congr_ae
  exact .of_forall fun x => by ring

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actualThirdCumulant_swap_first
#print axioms KLS.DeterministicBridgeNext.actualThirdCumulant_swap_last
#print axioms KLS.DeterministicBridgeNext.actualThirdCumulant_cyclic

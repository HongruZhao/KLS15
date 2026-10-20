import CubicCreationAdjointAlgebra
import ActualSymmetricQuadraticNoise

/-! Genuine cubic creation norm from the actual one-slot8 and distinct-slot4
bounds, for every symmetric quadratic input tensor. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLS.TensorEnergy
open KLSBelow25.CubicSymmetricNoise KLSBelow25.CubicCreation
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def actualThirdCubicArray (μ : Measure (Space n)) : Array3 (Fin n) :=
  fun i j k => thirdCumulantMatrix μ (MomentMap.coordinateVector i) j k

def lawCubicSlotArray (μ : Measure (Space n)) (H : Matrix (Fin n) (Fin n) ℝ) : Array3 (Fin n) :=
  fun i j k => ∑ l, actualThirdCubicArray μ i j l*H l k

 theorem lawCubicSlotArray_first_symmetry (μ : Measure (Space n)) (H : Matrix (Fin n) (Fin n) ℝ) :
    ∀ i j k,lawCubicSlotArray μ H i j k=lawCubicSlotArray μ H j i k := by
  intro i j k
  unfold lawCubicSlotArray actualThirdCubicArray
  simp_rw [actualThirdCumulant_swap_first μ i j]

 theorem matrix_tensor_coordinate_symmetric (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ i j,H i j=H j i) :
    CoordinateTensorSymmetric (fun a : Fin 2→Fin n => H (a 0) (a 1)) := by
  intro s t a
  fin_cases s <;> fin_cases t <;> simp [hH]

 theorem lawCubicSlotArray_slot_zero (μ : Measure (Space n)) (H : Matrix (Fin n) (Fin n) ℝ)
    (i j k : Fin n) :
    coordinateSlot (0 : Fin 2) (thirdCumulantMatrix μ (MomentMap.coordinateVector i))
      (fun a : Fin 2→Fin n => H (a 0) (a 1)) ![j,k]=lawCubicSlotArray μ H i j k := by
  rw [coordinateSlot_zero_pair]
  rfl

 theorem lawCubicSlotArray_slot_one (μ : Measure (Space n)) (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ i j,H i j=H j i) (i j k : Fin n) :
    coordinateSlot (1 : Fin 2) (thirdCumulantMatrix μ (MomentMap.coordinateVector i))
      (fun a : Fin 2→Fin n => H (a 0) (a 1)) ![j,k]=lawCubicSlotArray μ H i k j := by
  rw [coordinateSlot_one_pair]
  unfold lawCubicSlotArray actualThirdCubicArray
  exact Finset.sum_congr rfl fun l _ => by simp only [Matrix.cons_val_zero,Matrix.cons_val_one]; rw [hH j l]

 theorem lawCubicSlotArray_square_le_eight {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (H : Matrix (Fin n) (Fin n) ℝ) :
    square (lawCubicSlotArray μ H)≤8*matrixSquare H := by
  have hh := thirdCumulant_tensor_single_slot_le_eight hμ (0 : Fin 2)
    (fun a : Fin 2→Fin n => H (a 0) (a 1))
  simp only [←coordinateSlot_eq_tensorSlot,dotProduct,sum_fin_two_coordinates,
    lawCubicSlotArray_slot_zero,←pow_two] at hh
  simpa only [square,tripleSum,matrixSquare,Matrix.cons_val_zero,Matrix.cons_val_one] using hh

 theorem lawCubicSlotArray_cross_le_four {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : ∀ i j,H i j=H j i) :
    cross (lawCubicSlotArray μ H)≤4*matrixSquare H := by
  have hh := thirdCumulant_distinct_slot_pairing_le_four hμ
    (matrix_tensor_coordinate_symmetric H hH) (s:=(0 : Fin 2)) (t:=1) (by decide)
  simp only [sum_fin_two_coordinates,lawCubicSlotArray_slot_zero,
    lawCubicSlotArray_slot_one μ H hH] at hh
  simpa only [cross,tripleSum,matrixSquare,Matrix.cons_val_zero,Matrix.cons_val_one] using hh

 theorem actual_cubic_creation_square_le {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : ∀ i j,H i j=H j i) :
    square (creation (actualThirdCubicArray μ) H)≤48*matrixSquare H := by
  have hq := lawCubicSlotArray_square_le_eight hμ H
  have hr := lawCubicSlotArray_cross_le_four hμ H hH
  have he : square (creation (actualThirdCubicArray μ) H)=
      (9/4 : ℝ)*square (symPart (lawCubicSlotArray μ H)) := by
    unfold square
    rw [←tripleSum_smul]
    congr 1
    funext i j k
    unfold creation symPart lawCubicSlotArray
    ring
  rw [he,symPart_square _ (lawCubicSlotArray_first_symmetry μ H)]
  nlinarith

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actual_cubic_creation_square_le

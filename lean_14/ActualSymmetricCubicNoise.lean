import ActualCubicCreationBound
import QuarticSymmetricNoiseAlgebra
import FinThreeCoordinateEnumeration
import QuarticDisjointCreationTrace

/-! Full symmetry of the genuine fourth Appell coefficient, together with
the genuine cubic creation/annihilation bound, improves rank-three noise. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLS.TensorEnergy
open KLSBelow25.QuarticSymmetricNoise
variable {n : ℕ}
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

def actualQuarticSlotArray (μ : Measure (Space n)) (f : Space n → ℝ) : Array4 (Fin n) :=
  fun i j k l => ∑ m, actualThirdCubicArray μ i j m*actualCubicNextArray μ f m k l

def actualQuarticNextArray (μ : Measure (Space n)) (f : Space n → ℝ) : Array4 (Fin n) :=
  fun i j k l => actualAppellCoefficient μ f 4 ![i,j,k,l]

theorem actualQuarticSlotArray_first_symmetry (μ : Measure (Space n)) (f : Space n → ℝ) :
    ∀ i j k l, actualQuarticSlotArray μ f i j k l=actualQuarticSlotArray μ f j i k l := by
  intro i j k l
  unfold actualQuarticSlotArray actualThirdCubicArray
  simp_rw [actualThirdCumulant_swap_first μ i j]

theorem actualQuarticSlotArray_last_symmetry {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    ∀ i j k l, actualQuarticSlotArray μ f i j k l=actualQuarticSlotArray μ f i j l k := by
  intro i j k l
  unfold actualQuarticSlotArray
  simp_rw [actualCubicNextArray_last_symmetry hLC hf]

theorem actualQuarticNextArray_first_symmetry {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    ∀ i j k l, actualQuarticNextArray μ f i j k l=actualQuarticNextArray μ f j i k l := by
  intro i j k l
  have hh := actualAppellCoefficient_symmetric hLC hf (0 : Fin 4) 1 ![i,j,k,l]
  have he : (![i,j,k,l] ∘ Equiv.swap (0 : Fin 4) 1)=![j,i,k,l] := by
    ext a; fin_cases a <;> simp [Equiv.swap_apply_def]
  rw [he] at hh
  exact hh.symm

theorem actualQuarticNextArray_middle_symmetry {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    ∀ i j k l, actualQuarticNextArray μ f i j k l=actualQuarticNextArray μ f i k j l := by
  intro i j k l
  have hh := actualAppellCoefficient_symmetric hLC hf (1 : Fin 4) 2 ![i,j,k,l]
  have he : (![i,j,k,l] ∘ Equiv.swap (1 : Fin 4) 2)=![i,k,j,l] := by
    ext a; fin_cases a <;> simp [Equiv.swap_apply_def]
  rw [he] at hh
  exact hh.symm

theorem actualQuarticNextArray_last_symmetry {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    ∀ i j k l, actualQuarticNextArray μ f i j k l=actualQuarticNextArray μ f i j l k := by
  intro i j k l
  have hh := actualAppellCoefficient_symmetric hLC hf (2 : Fin 4) 3 ![i,j,k,l]
  have he : (![i,j,k,l] ∘ Equiv.swap (2 : Fin 4) 3)=![i,j,l,k] := by
    ext a; fin_cases a <;> simp [Equiv.swap_apply_def]
  rw [he] at hh
  exact hh.symm

theorem actualQuarticSlotArray_slot_zero (μ : Measure (Space n)) (f : Space n → ℝ)
    (i j k l : Fin n) :
    coordinateSlot (0 : Fin 3) (thirdCumulantMatrix μ (MomentMap.coordinateVector i))
      (actualAppellCoefficient μ f 3) ![j,k,l]=actualQuarticSlotArray μ f i j k l := by
  rw [coordinateSlot_zero_triple]
  rfl

theorem actualQuarticSlotArray_slot_one {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (i j k l : Fin n) :
    coordinateSlot (1 : Fin 3) (thirdCumulantMatrix μ (MomentMap.coordinateVector i))
      (actualAppellCoefficient μ f 3) ![j,k,l]=actualQuarticSlotArray μ f i k j l := by
  rw [coordinateSlot_one_triple]
  unfold actualQuarticSlotArray actualThirdCubicArray
  apply Finset.sum_congr rfl
  intro m _
  change _*actualCubicNextArray μ f j m l=_*actualCubicNextArray μ f m j l
  rw [actualCubicNextArray_first_symmetry hLC hf]

theorem actualQuarticSlotArray_slot_two {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (i j k l : Fin n) :
    coordinateSlot (2 : Fin 3) (thirdCumulantMatrix μ (MomentMap.coordinateVector i))
      (actualAppellCoefficient μ f 3) ![j,k,l]=actualQuarticSlotArray μ f i l j k := by
  rw [coordinateSlot_two_triple]
  unfold actualQuarticSlotArray actualThirdCubicArray
  apply Finset.sum_congr rfl
  intro m _
  change _*actualCubicNextArray μ f j k m=_*actualCubicNextArray μ f m j k
  rw [actualCubicNextArray_last_symmetry hLC hf j k m,
    actualCubicNextArray_first_symmetry hLC hf j m k]

theorem actualQuarticSlotArray_square_le_eight {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (f : Space n → ℝ) :
    square (actualQuarticSlotArray μ f)≤8*actualAppellEnergy μ f 3 := by
  have hh := thirdCumulant_tensor_single_slot_le_eight hμ (0 : Fin 3)
    (actualAppellCoefficient μ f 3)
  simp only [←coordinateSlot_eq_tensorSlot,dotProduct,sum_fin_three_coordinates,
    actualQuarticSlotArray_slot_zero,←pow_two] at hh
  simpa only [square,quadSum,actualAppellEnergy,sum_fin_three_coordinates] using hh

theorem actualQuarticSlotArray_cross_le_four {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    cross (actualQuarticSlotArray μ f)≤4*actualAppellEnergy μ f 3 := by
  have : IsProbabilityMeasure μ := hμ.isProb
  have hh := thirdCumulant_distinct_slot_pairing_le_four hμ
    (actualAppellCoefficient_symmetric hμ.logConcave hf) (s:=(0 : Fin 3)) (t:=1) (by decide)
  simp only [sum_fin_three_coordinates,actualQuarticSlotArray_slot_zero,
    actualQuarticSlotArray_slot_one hμ.logConcave hf] at hh
  simpa only [cross,quadSum,actualAppellEnergy,sum_fin_three_coordinates] using hh

theorem actualQuarticSlotArray_disjoint_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    disjoint (actualQuarticSlotArray μ f)≤(16/3 : ℝ)*actualAppellEnergy μ f 3 := by
  have : IsProbabilityMeasure μ := hμ.isProb
  have hh := KLSBelow25.CubicCreation.annihilation_trace_square_le
    (actualThirdCubicArray μ) (actualCubicNextArray μ f)
    (actualCubicNextArray_first_symmetry hμ.logConcave hf)
    (actualCubicNextArray_last_symmetry hμ.logConcave hf)
    (fun H hH => actual_cubic_creation_square_le hμ H hH)
  rw [actualCubicNextArray_square μ f] at hh
  unfold actualQuarticSlotArray
  rw [KLSBelow25.QuarticSymmetricNoise.disjoint_creation_trace]
  exact hh

theorem actualQuarticNextArray_square (μ : Measure (Space n)) (f : Space n → ℝ) :
    square (actualQuarticNextArray μ f)=actualAppellEnergy μ f 4 := by
  simp only [square,quadSum,actualQuarticNextArray,actualAppellEnergy,
    sum_fin_four_coordinates]

theorem actualQuartic_noise_eq {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    noise (actualQuarticSlotArray μ f) (actualQuarticNextArray μ f)=
      ∑ i : Fin n, energyNoiseCorrection (actualAppellCoefficient μ f 3)
        (thirdCumulantMatrix μ (MomentMap.coordinateVector i))
        (fun a => actualAppellCoefficient μ f 4 (Fin.cons i a)) := by
  have hfin3 {E : Type} [AddCommMonoid E] (F : Fin 3 → E) :
      (∑ i,F i)=F 0+F 1+F 2 := by
    rw [Fin.sum_univ_succ,Fin.sum_univ_two]
    simp only [Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
    abel
  have hsum (H : Matrix (Fin n) (Fin n) ℝ) (T : (Fin 3 → Fin n) → ℝ) :
      tensorSlotSum H *ᵥ T=coordinateSlot (0 : Fin 3) H T+
        coordinateSlot 1 H T+coordinateSlot 2 H T := by
    simp only [tensorSlotSum,hfin3,Matrix.add_mulVec,coordinateSlot_eq_tensorSlot]
  unfold noise quadSum energyNoiseCorrection
  simp only [hsum,dotProduct,hfin3,
    sum_fin_three_coordinates,←coordinateSlot_eq_tensorSlot,Pi.add_apply,
    actualQuarticSlotArray_slot_zero,actualQuarticSlotArray_slot_one hLC hf,
    actualQuarticSlotArray_slot_two hLC hf,←pow_two]
  apply Finset.sum_congr rfl
  intro i _
  simp only [←Finset.sum_add_distrib,←Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  have he : Fin.cons i ![j,k,l]=![i,j,k,l] := by ext a; fin_cases a <;> rfl
  simp only [he,actualQuarticNextArray]
  ring

theorem actualAppell_noiseCorrection_lower_three_symmetric {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    {β : ℝ} (hβ0 : (1 : ℝ)/2≤β) (hβ1 : β<1) :
    β*actualAppellEnergy μ f 4-(44/(1-β)-36)*actualAppellEnergy μ f 3 ≤
      ∑ i : Fin n, energyNoiseCorrection (actualAppellCoefficient μ f 3)
        (thirdCumulantMatrix μ (MomentMap.coordinateVector i))
        (fun a => actualAppellCoefficient μ f 4 (Fin.cons i a)) := by
  have : IsProbabilityMeasure μ := hμ.isProb
  have hh := lower_of_bounds hβ0 hβ1 (actualQuarticSlotArray μ f) (actualQuarticNextArray μ f)
    (actualQuarticSlotArray_first_symmetry μ f)
    (actualQuarticSlotArray_last_symmetry hμ.logConcave hf)
    (actualQuarticNextArray_first_symmetry hμ.logConcave hf)
    (actualQuarticNextArray_middle_symmetry hμ.logConcave hf)
    (actualQuarticNextArray_last_symmetry hμ.logConcave hf)
    (actualQuarticSlotArray_square_le_eight hμ f)
    (actualQuarticSlotArray_cross_le_four hμ hf)
    (actualQuarticSlotArray_disjoint_le hμ hf)
  rwa [actualQuarticNextArray_square,actualQuartic_noise_eq hμ.logConcave hf] at hh

theorem actualCovarianceAppellEnergy_generator_lower_three_symmetric
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {β : ℝ}
    (hβ0 : (1 : ℝ)/2≤β) (hβ1 : β<1) :
    β*actualAppellEnergy μ f 4-(44/(1-β)-33)*actualAppellEnergy μ f 3-
      2*(actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellLowerDriftTensor μ f 3) ≤
    actualAppellEnergyHeatGenerator μ f 3 := by
  have hh := actualAppell_noiseCorrection_lower_three_symmetric hμ hf hβ0 hβ1
  unfold actualAppellEnergyHeatGenerator
  rw [actualCovarianceAppellEnergy_generator_exact hμ hf 3]
  norm_num only [Nat.cast_ofNat]
  linarith

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualCovarianceAppellEnergy_generator_lower_three_symmetric

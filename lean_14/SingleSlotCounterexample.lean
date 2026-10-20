import SingleSlotCounterexampleEnergy
import SingleSlotCounterexampleLogConcave

/-! A concrete admissible isotropic log-concave law disproves the universal
single-slot third-cumulant cap four. This is an intermediate contraction
counterexample, not a counterexample to Poincaré constant four. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ENNReal
namespace KLSImprovement.SingleSlotCounterexample
open KLS
local instance :IsProbabilityMeasure rawMeasure := raw_isProbability

theorem isotropicMeasure_logConcave :measureLogConcave isotropicMeasure := by
  change measureLogConcave (affineMatrixMeasure rawMeasure whiteningMatrix whiteningTranslation)
  exact raw_logConcave.affineMatrixMeasure whiteningMatrix whiteningTranslation

theorem isotropicMeasure_admissible :admissibleMeasure isotropicMeasure :=
  ⟨isotropicMeasure_isProbability,isotropicMeasure_logConcave,isotropicMeasure_isIsotropic⟩

theorem exists_admissible_counterexample_to_single_slot_four :
    ∃ μ:Measure (Space 2),admissibleMeasure μ ∧
      ¬((4:ℝ) • (1:Matrix (Fin 2) (Fin 2) ℝ)-
        ∑k:Fin 2,thirdCumulantMatrix μ (MomentMap.coordinateVector k)*
          thirdCumulantMatrix μ (MomentMap.coordinateVector k)).PosSemidef :=
  ⟨isotropicMeasure,isotropicMeasure_admissible,isotropicMeasure_not_cap_four⟩

theorem universal_single_slot_four_is_false :
    ¬∀ μ:Measure (Space 2),admissibleMeasure μ →
      ((4:ℝ) • (1:Matrix (Fin 2) (Fin 2) ℝ)-
        ∑k:Fin 2,thirdCumulantMatrix μ (MomentMap.coordinateVector k)*
          thirdCumulantMatrix μ (MomentMap.coordinateVector k)).PosSemidef := by
  intro h
  exact isotropicMeasure_not_cap_four (h isotropicMeasure isotropicMeasure_admissible)

end KLSImprovement.SingleSlotCounterexample
#print axioms KLSImprovement.SingleSlotCounterexample.isotropicMeasure_admissible
#print axioms KLSImprovement.SingleSlotCounterexample.exists_admissible_counterexample_to_single_slot_four
#print axioms KLSImprovement.SingleSlotCounterexample.universal_single_slot_four_is_false

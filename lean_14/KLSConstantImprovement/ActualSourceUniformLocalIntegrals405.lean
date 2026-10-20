import KLSConstantImprovement.ActualSourceThirdUniformEnergy405
import KLS.WeightedLocalDistribution

/-! Quantitative local Lebesgue control from actual source potentials.
The same common upper potential bound transfers global source estimates
to the ordinary local estimates required by raw-H1 compactness. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal ContDiff ENNReal
namespace KLSConstantImprovement.ActualSourceUniformLocalIntegrals405
open KLS ActualBoundedCanonicalSource ActualSourceThirdUniformEnergy405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_local_nonnegative_integral_bound (d : SourceData μ)
    {E : Set (Space n)} (hE : MeasurableSet E) {P : ℝ}
    (hp : ∀ x ∈ E, d.potential x ≤ P)
    {f : Space n → ℝ} (hf : Integrable f (potentialMeasure d.potential))
    (hn : ∀ x, 0 ≤ f x) :
    Integrable f (volume.restrict E) ∧
      (∫ x in E, f x) ≤ Real.exp P * ∫ x, f x ∂potentialMeasure d.potential := by
  have hm := restrict_volume_le_exp_smul_potentialMeasure
    d.source_C1.continuous.measurable hE hp
  have hi := hf.smul_measure (c := ENNReal.ofReal (Real.exp P)) ENNReal.ofReal_ne_top
  refine ⟨hi.mono_measure hm, ?_⟩
  have h := integral_mono_measure hm (Eventually.of_forall hn) hi
  simpa only [integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul] using h

theorem actual_third_entry_local_square_integral (d : SourceData μ)
    (hiso : IsIsotropic μ) {B P : ℝ}
    (hB : 16 / d.targetConvexityConstant ≤ B)
    {E : Set (Space n)} (hE : MeasurableSet E)
    (hp : ∀ x ∈ E, d.potential x ≤ P) (k i j : Fin n) :
    Integrable (fun x => d.third x k i j ^ 2) (volume.restrict E) ∧
      (∫ x in E, d.third x k i j ^ 2) ≤ Real.exp P * B ^ 2 := by
  obtain ⟨hi, hb⟩ := actual_third_entry_global_square_integral d hiso hB k i j
  obtain ⟨hl, hle⟩ := actual_local_nonnegative_integral_bound d hE hp hi
    (fun x => sq_nonneg (d.third x k i j))
  exact ⟨hl, hle.trans (mul_le_mul_of_nonneg_left hb (Real.exp_nonneg P))⟩

end KLSConstantImprovement.ActualSourceUniformLocalIntegrals405
#print axioms KLSConstantImprovement.ActualSourceUniformLocalIntegrals405.actual_local_nonnegative_integral_bound
#print axioms KLSConstantImprovement.ActualSourceUniformLocalIntegrals405.actual_third_entry_local_square_integral

import KLSConstantImprovement.ActualWeakKatoExcess405
import KLSConstantImprovement.ActualTargetCutoffErrorBudget405
import KLSConstantImprovement.ActualSignedCoordinateExcess405

/-! Specialize the genuine uncapped weak-Kato excess test to actual target
pullbacks and the literal square root of natural inverse mass. All cutoff,
mass and error integrability domains are paid by the actual source and
unconditional Gaffney bound. Only the weak Kato solution remains input. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
namespace KLSConstantImprovement.ActualTargetCutoffKatoExcess405
open KLS ActualBoundedCanonicalSource ActualWeakKatoExcess405 ActualWeakKatoCompactExcess405
open ActualTargetCutoffErrorBudget405 ActualSignedCoordinateExcess405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405 ActualSourceBoundedMassCutoffs405
open ActualSourcePullbackMetricGradient405 ActualTargetPullbackCutoffEnergy405 ActualCompactRawMetricGraph
open ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricOrdinaryGraph ActualWeakCanonicalMetricCore
open ActualSourceCompactConnectionDomains405 ActualSourceCompactConnectionAbsorption405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_sqrt_natural_mass_local_L2 (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0)
    (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (fun x => Real.sqrt (sourceVectorMass d.potential (naturalCanonicalFlux d g) x)) 2
      (volume.restrict E) := by
  have hMi := (actual_natural_mass_integrable_and_bound d hn g hg).1
  have hM : Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g)) (volume.restrict E) :=
    memLp_one_iff_integrable.mp (KLS.MemLp.restrict_volume_of_potentialMeasure
      (memLp_one_iff_integrable.mpr hMi) d.source_C1.continuous hE)
  have hm := Real.continuous_sqrt.comp_aestronglyMeasurable hM.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply hM.congr
  have hnM := (sourceVectorMass_nonnegative_ae d (naturalCanonicalFlux d g)).filter_mono
    (volume_absolutelyContinuous_potentialMeasure d.source_C1.continuous).ae_le
  filter_upwards [ae_restrict_of_ae hnM] with x hx
  exact (Real.sq_sqrt hx).symm

theorem pullback_metric_square_eq_raw_cutoff_square (d : SourceData μ) (χ : Space n → ℝ) :
    pullbackMetricSquare d χ =ᵐ[potentialMeasure d.potential]
      rawCutoffSquare d (pullbackRawGradient d χ) := by
  filter_upwards [d.hessian_ae_source] with x hp
  let R := canonicalMetricRoot d.potential x
  let z : Fin n → ℝ := fun i => pullbackRawGradient d χ i x
  have he : (R *ᵥ z) ⬝ᵥ (R *ᵥ z) =
      z ⬝ᵥ ((coordinateHessian d.potential x)⁻¹ *ᵥ z) := by
    rw [← Matrix.dotProduct_transpose_mulVec R z (R *ᵥ z), Matrix.mulVec_mulVec,
      canonicalMetricRoot_gram_at hp.1]
  simpa only [pullbackMetricSquare, rawCutoffSquare, rawCanonicalMetricDerivative, R, z,
    dotProduct, Matrix.mulVec, pow_two] using he

theorem actual_target_pullback_excess_of_weak_sqrt_mass_Kato
    (d : SourceData μ) (hn : 1 ≤ n) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0)
    {B : ℝ} (hB : 0 ≤ B) (Dw : Fin n → Space n → ℝ)
    (hDw : ∀ i E, IsCompact E → MemLp (Dw i) 2 (volume.restrict E))
    (hww : ∀ i, HasLocalWeakCoordinateDerivative
      (fun x => Real.sqrt (sourceVectorMass d.potential (naturalCanonicalFlux d g) x)) (Dw i) i)
    (hweak : ∀ ψ : Space n → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∀ x, 0 ≤ ψ x) →
      (∑ i, ∫ x, rawKatoFlux d Dw i x * coordinateDerivative ψ i x ∂potentialMeasure d.potential) ≤
        ∫ x, (B-Real.sqrt (sourceVectorMass d.potential (naturalCanonicalFlux d g) x)/2)*ψ x
          ∂potentialMeasure d.potential)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hc : HasCompactSupport (fun x => χ (gradient d.potential x))) :
    Integrable (fun x => χ (gradient d.potential x)^2 * naturalMassExcess d g (2*B) x^2)
      (potentialMeasure d.potential) ∧
      (∫ x, χ (gradient d.potential x)^2 * naturalMassExcess d g (2*B) x^2
        ∂potentialMeasure d.potential) ≤
        4*(∫ x, sourceVectorMass d.potential (naturalCanonicalFlux d g) x *
          pullbackMetricSquare d χ x ∂potentialMeasure d.potential) := by
  have hMi := (actual_natural_mass_integrable_and_bound d hn g hg).1
  have hΓtop : MemLp (pullbackMetricSquare d χ) ∞ (potentialMeasure d.potential) := by
    apply memLp_finsetSum Finset.univ
    intro i _
    have ht := pullback_raw_metric_gradient_memLp_top d hχ i
    have hh : MemLp (fun x => rawCanonicalMetricDerivative d.potential (pullbackRawGradient d χ) i x *
      rawCanonicalMetricDerivative d.potential (pullbackRawGradient d χ) i x) ∞
        (potentialMeasure d.potential) := ht.mul ht
    change MemLp (fun x => rawCanonicalMetricDerivative d.potential (pullbackRawGradient d χ) i x *
      rawCanonicalMetricDerivative d.potential (pullbackRawGradient d χ) i x) ∞ _ at hh
    simpa only [pow_two] using hh
  have hcost : Integrable (fun x => sourceVectorMass d.potential (naturalCanonicalFlux d g) x *
      pullbackMetricSquare d χ x) (potentialMeasure d.potential) := hMi.mul_of_top_left hΓtop
  have hDχ (i : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (pullbackRawGradient d χ i) ∞ (volume.restrict E) := by
    have hh := memLp_top_of_absoluteContinuity
      (volume_absolutelyContinuous_potentialMeasure d.source_C1.continuous)
      (d.pullback_weak_derivative_memLp hχ i ∞)
    exact hh.restrict E
  have heq : (fun x => sourceVectorMass d.potential (naturalCanonicalFlux d g) x *
      pullbackMetricSquare d χ x) =ᵐ[potentialMeasure d.potential]
      (fun x => Real.sqrt (sourceVectorMass d.potential (naturalCanonicalFlux d g) x)^2 *
        rawCutoffSquare d (pullbackRawGradient d χ) x) := by
    filter_upwards [sourceVectorMass_nonnegative_ae d (naturalCanonicalFlux d g),
      pullback_metric_square_eq_raw_cutoff_square d χ] with x hnM hΓ
    rw [Real.sq_sqrt hnM, hΓ]
  have he := compact_excess_of_actual_weak_Kato d hB (actual_sqrt_natural_mass_local_L2 d hn g hg)
    hDw hww (Eventually.of_forall fun x => Real.sqrt_nonneg _) hweak
    (hχ.continuous.comp d.gradient_lipschitz.continuous) hc hDχ
    (d.pullback_hasLocalWeakCoordinateDerivative hχ) (hcost.congr heq)
  refine ⟨he.1, ?_⟩
  rw [← integral_congr_ae heq] at he
  exact he.2

end KLSConstantImprovement.ActualTargetCutoffKatoExcess405
#print axioms KLSConstantImprovement.ActualTargetCutoffKatoExcess405.actual_sqrt_natural_mass_local_L2
#print axioms KLSConstantImprovement.ActualTargetCutoffKatoExcess405.pullback_metric_square_eq_raw_cutoff_square
#print axioms KLSConstantImprovement.ActualTargetCutoffKatoExcess405.actual_target_pullback_excess_of_weak_sqrt_mass_Kato

import KLSConstantImprovement.ActualKatoCutoffError405

/-! The exact limiting Kato integrand and forcing admit all actual
compact weighted pairings, before taking the common dual cutoff limit. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualKatoCompactPairings405
open KLS ActualBoundedCanonicalSource ActualKatoJointPointwise405 ActualKatoNonlinearDomains405
open ActualKatoLocalDomains405 ActualKatoCoefficientBounds405 ActualDualKatoMultiplier405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405 ActualSmoothKatoRegularizer405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem naturalKatoForcing_local_integrable (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hMi : Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g)) (potentialMeasure d.potential))
    (Dg : Fin n → Space n → ℝ) (hDg : ∀ a, MemLp (Dg a) 2 (potentialMeasure d.potential))
    {ε : ℝ} (hε : 0 < ε) : LocallyIntegrable (naturalKatoForcing d g ε Dg) volume := by
  have hMn := (natural_mass_nonnegative_ae d g).filter_mono
    (volume_absolutelyContinuous_potentialMeasure d.source_C1.continuous).ae_le
  apply locallyIntegrable_iff.mpr
  intro E hE
  have hM := memLp_one_iff_integrable.mp (KLS.MemLp.restrict_volume_of_potentialMeasure
    (memLp_one_iff_integrable.mpr hMi) d.source_C1.continuous hE)
  have htop : MemLp (fun x => 2 * katoFirst ε (sourceVectorMass d.potential (naturalCanonicalFlux d g) x))
      ∞ (volume.restrict E) := by
    have hh : MemLp (fun x => katoFirst ε (sourceVectorMass d.potential (naturalCanonicalFlux d g) x))
        ∞ (volume.restrict E) := by
      apply memLp_top_of_bound ((katoFirst_contDiff hε).continuous.comp_aestronglyMeasurable
        hM.aestronglyMeasurable) (1 / (2 * Real.sqrt ε))
      filter_upwards [ae_restrict_of_ae hMn] with x hx
      rw [Real.norm_of_nonneg (katoFirst_fixed_bound hε hx).1]
      exact (katoFirst_fixed_bound hε hx).2
    exact hh.const_mul 2
  have hi : Integrable (fun x => ∑ j : Fin n, Dg j x * naturalCanonicalFlux d g j x) (volume.restrict E) :=
    integrable_finsetSum Finset.univ fun j _ =>
      (KLS.MemLp.restrict_volume_of_potentialMeasure (hDg j) d.source_C1.continuous hE).integrable_mul (hu j E hE)
  exact hi.mul_of_top_right htop

theorem naturalKato_compact_pairing_domains (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) {ε : ℝ}
    (hFlux : ∀ a E, IsCompact E → MemLp (naturalKatoMetricFlux d g Du ε a) 2 (volume.restrict E))
    (hDensity : LocallyIntegrable (naturalKatoDensity d g Du ε) volume)
    (Dg : Fin n → Space n → ℝ) (hForce : LocallyIntegrable (naturalKatoForcing d g ε Dg) volume)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∀ a, Integrable (fun x => naturalKatoMetricFlux d g Du ε a x * coordinateDerivative ψ a x)
      (potentialMeasure d.potential)) ∧
      Integrable (fun x => ψ x * naturalKatoDensity d g Du ε x) (potentialMeasure d.potential) ∧
      Integrable (naturalKatoWeakIntegrand d g Du ε ψ) (potentialMeasure d.potential) ∧
      Integrable (fun x => ψ x * naturalKatoForcing d g ε Dg x) (potentialMeasure d.potential) := by
  have hflux (a : Fin n) : Integrable (fun x => naturalKatoMetricFlux d g Du ε a x *
      coordinateDerivative ψ a x) (potentialMeasure d.potential) :=
    integrable_raw_mul_compact_potential d.source_C1.continuous
      (locallyIntegrable_of_memLp_two_on_compacts (hFlux a))
      (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) a).continuous
      (hasCompactSupport_coordinateDerivative hc a)
  have hD : Integrable (fun x => ψ x * naturalKatoDensity d g Du ε x) (potentialMeasure d.potential) := by
    have he := integrable_raw_mul_compact_potential d.source_C1.continuous hDensity hψ.continuous hc
    exact he.congr (Eventually.of_forall fun x => mul_comm _ _)
  have hI : Integrable (naturalKatoWeakIntegrand d g Du ε ψ) (potentialMeasure d.potential) :=
    hD.add (integrable_finsetSum Finset.univ fun a _ => hflux a)
  have hF : Integrable (fun x => ψ x * naturalKatoForcing d g ε Dg x) (potentialMeasure d.potential) := by
    have he := integrable_raw_mul_compact_potential d.source_C1.continuous hForce hψ.continuous hc
    exact he.congr (Eventually.of_forall fun x => mul_comm _ _)
  exact ⟨hflux, hD, hI, hF⟩

end KLSConstantImprovement.ActualKatoCompactPairings405
#print axioms KLSConstantImprovement.ActualKatoCompactPairings405.naturalKatoForcing_local_integrable
#print axioms KLSConstantImprovement.ActualKatoCompactPairings405.naturalKato_compact_pairing_domains

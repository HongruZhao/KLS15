import KLSConstantImprovement.ActualKatoPointwiseBounds405

/-! The actual natural inverse satisfies the local regularized Kato
subsolution inequality. Every nonlinear weak test and limiting domain is
constructed from the same Gaffney Jacobian. No natural mass bound is an
input. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualRegularizedWeakKato405
open KLS ActualBoundedCanonicalSource ActualKatoPointwiseBounds405 ActualRegularizedWeakBochner405
open ActualKatoJointPointwise405 ActualKatoNonlinearDomains405 ActualKatoLocalDomains405
open ActualNaturalCovariantEnergy405 ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
open ActualSourceNaturalHessian405 ActualSourceConnectionFields405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_regularized_weak_Kato (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i a E, IsCompact E → MemLp (Du i a) 2 (volume.restrict E))
    (hw : ∀ i a, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i a) a)
    (hC : ∀ i a E, IsCompact E → MemLp (fun x => naturalCanonicalHessian d g Du x i a) 2 (volume.restrict E))
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i a => Du i a x)).IsSymm)
    (hMi : Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g)) (potentialMeasure d.potential))
    (hEloc : LocallyIntegrable (naturalCovariantEnergy d g Du) volume)
    (hΓloc : LocallyIntegrable (sourceConnectionGamma d (naturalCanonicalFlux d g)) volume)
    (Dg : Fin n → Space n → ℝ)
    (hgw : ∀ a, HasLocalWeakCoordinateDerivative (g : Space n → ℝ) (Dg a) a)
    (hDg : ∀ a, MemLp (Dg a) 2 (potentialMeasure d.potential))
    {B : ℝ} (hB : 0 ≤ B)
    (hgrad : ∀ᵐ x ∂potentialMeasure d.potential,
      (fun a => Dg a x) ⬝ᵥ ((coordinateHessian d.potential x)⁻¹ *ᵥ (fun a => Dg a x)) ≤ B ^ 2)
    {ε : ℝ} (hε : 0 < ε)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) (hψn : ∀ x, 0 ≤ ψ x) :
    (∑ a : Fin n, ∫ x, naturalKatoMetricFlux d g Du ε a x * coordinateDerivative ψ a x
      ∂potentialMeasure d.potential) ≤
        ∫ x, (B + Real.sqrt ε / 2 - naturalKatoValue d g ε x / 2) * ψ x
          ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let ν := potentialMeasure d.potential
  obtain ⟨hFI, hDI, hBI, he⟩ := actual_regularized_weak_Bochner d hn g hg Du hu hDu hw hC
    hcomp hMi hEloc hΓloc Dg hgw hDg hε (hψ.of_le (by norm_num)) hc
  have hψI : Integrable ψ ν :=
    (show MemLp ψ 1 ν from hψ.continuous.memLp_of_hasCompactSupport hc).integrable (by norm_num)
  have hV : Integrable (fun x => ψ x * naturalKatoValue d g ε x) ν := by
    have hh := integrable_raw_mul_compact_potential d.source_C1.continuous
      (locallyIntegrable_of_memLp_two_on_compacts (naturalKatoValue_local_L2 d g hMi hε)) hψ.continuous hc
    exact hh.congr (Eventually.of_forall fun x => mul_comm _ _)
  have hR : Integrable (fun x => (B + Real.sqrt ε / 2 - naturalKatoValue d g ε x / 2) * ψ x) ν := by
    have hi := (hψI.const_mul (B + Real.sqrt ε / 2)).sub (hV.div_const 2)
    exact hi.congr (Eventually.of_forall fun x => by
      change (B + Real.sqrt ε / 2) * ψ x - (ψ x * naturalKatoValue d g ε x) / 2 =
        (B + Real.sqrt ε / 2 - naturalKatoValue d g ε x / 2) * ψ x
      ring)
  have hpoint : ∀ᵐ x ∂ν,
      ψ x * naturalKatoForcing d g ε Dg x - ψ x * naturalKatoDensity d g Du ε x ≤
        (B + Real.sqrt ε / 2 - naturalKatoValue d g ε x / 2) * ψ x := by
    filter_upwards [naturalKatoForcing_upper_ae d g Dg hB hε hgrad,
      naturalKatoDensity_lower_ae d g Du hcomp hε] with x hF hD
    have h1 := mul_le_mul_of_nonneg_left hF (hψn x)
    have h2 := mul_le_mul_of_nonneg_left hD (hψn x)
    nlinarith only [h1, h2]
  have hle := integral_mono_ae (hBI.sub hDI) hR hpoint
  change (∫ x, ψ x * naturalKatoForcing d g ε Dg x - ψ x * naturalKatoDensity d g Du ε x ∂ν) ≤ _ at hle
  rw [integral_sub hBI hDI] at hle
  linarith only [he, hle]

end KLSConstantImprovement.ActualRegularizedWeakKato405
#print axioms KLSConstantImprovement.ActualRegularizedWeakKato405.actual_regularized_weak_Kato

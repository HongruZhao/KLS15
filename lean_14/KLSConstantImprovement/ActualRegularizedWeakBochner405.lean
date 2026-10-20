import KLSConstantImprovement.ActualKatoCompactPairings405

/-! Exact nonlinear weak Bochner identity for the actual regularized mass.
The genuine compact dual test is removed by a paid dominated limit. There
is no bounded mass, classical Hessian, or strong operator core premise. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualRegularizedWeakBochner405
open KLS ActualBoundedCanonicalSource ActualKatoCompactPairings405 ActualKatoCutoffError405
open ActualKatoJointPointwise405 ActualKatoNonlinearDomains405 ActualKatoLocalDomains405
open ActualNaturalCovariantEnergy405 ActualNaturalDualJoint405 ActualDualBumpControl405
open ActualDualWeakBochner405 ActualDualKatoMultiplier405 ActualSmoothKatoRegularizer405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405 ActualSourceNaturalHessian405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_regularized_weak_Bochner (d : SourceData μ) (hn : 1 ≤ n)
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
    (hΓloc : LocallyIntegrable (ActualSourceConnectionFields405.sourceConnectionGamma d (naturalCanonicalFlux d g)) volume)
    (Dg : Fin n → Space n → ℝ)
    (hgw : ∀ a, HasLocalWeakCoordinateDerivative (g : Space n → ℝ) (Dg a) a)
    (hDg : ∀ a, MemLp (Dg a) 2 (potentialMeasure d.potential))
    {ε : ℝ} (hε : 0 < ε)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∀ a, Integrable (fun x => naturalKatoMetricFlux d g Du ε a x * coordinateDerivative ψ a x)
      (potentialMeasure d.potential)) ∧
      Integrable (fun x => ψ x * naturalKatoDensity d g Du ε x) (potentialMeasure d.potential) ∧
      Integrable (fun x => ψ x * naturalKatoForcing d g ε Dg x) (potentialMeasure d.potential) ∧
      (∑ a : Fin n, ∫ x, naturalKatoMetricFlux d g Du ε a x * coordinateDerivative ψ a x
        ∂potentialMeasure d.potential) +
          (∫ x, ψ x * naturalKatoDensity d g Du ε x ∂potentialMeasure d.potential) =
            ∫ x, ψ x * naturalKatoForcing d g ε Dg x ∂potentialMeasure d.potential := by
  let ν := potentialMeasure d.potential
  have hG := naturalKatoDerivative_local_L2 d g Du hu hDu hC hcomp hMi hEloc hε
  have hFlux := naturalKatoMetricFlux_local_L2 d g Du hG
  have hDensity := naturalKatoDensity_local_integrable d g Du hu hDu hC hcomp hMi hEloc hΓloc hε
  have hForce := naturalKatoForcing_local_integrable d g hu hMi Dg hDg hε
  obtain ⟨hFI, hDI, hAI, hBI⟩ := naturalKato_compact_pairing_domains d g Du hFlux hDensity Dg hForce hψ hc
  have hbm (k : ℕ) : AEStronglyMeasurable (dualSource d g (dualBump k)) ν := by
    have hb := actual_dual_compact_chain d g Du hu hDu hw hC (dualBump_contDiff k) (dualBump_compact k)
    exact (locallyIntegrable_of_memLp_two_on_compacts hb.2.1).aestronglyMeasurable.mono_ac
      (withDensity_absolutelyContinuous _ _)
  have hA := actual_dual_bump_integral_tendsto d g hbm hAI
  have hB := actual_dual_bump_integral_tendsto d g hbm hBI
  have hError := actual_Kato_bump_error_tendsto_zero d g Du hu hDu hw hC hFlux hψ hc
  have hEq (k : ℕ) :
      (∫ x, dualSource d g (dualBump k) x * naturalKatoWeakIntegrand d g Du ε ψ x ∂ν) +
        (∫ x, naturalKatoBumpError d g Du ε k ψ x ∂ν) =
          ∫ x, dualSource d g (dualBump k) x * (ψ x * naturalKatoForcing d g ε Dg x) ∂ν := by
    obtain ⟨_hleft, _hright, he⟩ := actual_dual_weak_Bochner d hn g hg Du hu hDu hw hC hMi Dg hgw hDg
      (katoJointMultiplier_contDiff_compact hε k).1 (katoJointMultiplier_contDiff_compact hε k).2 hψ hc
    have hl : (∫ x, dualBochnerIntegrand d g Du (katoJointMultiplier ε k) ψ x ∂ν) =
        (∫ x, dualSource d g (dualBump k) x * naturalKatoWeakIntegrand d g Du ε ψ x ∂ν) +
          (∫ x, naturalKatoBumpError d g Du ε k ψ x ∂ν) := by
      calc
        _ = ∫ x, dualSource d g (dualBump k) x * naturalKatoWeakIntegrand d g Du ε ψ x +
            naturalKatoBumpError d g Du ε k ψ x ∂ν :=
          integral_congr_ae (actual_Kato_common_bump_expansion_ae d g Du hcomp hε k ψ)
        _ = _ := integral_add (hA.1 k) (hError.1 k)
    have hr : (∫ x, ψ x * dualSource d g (katoJointMultiplier ε k) x *
        (∑ j : Fin n, Dg j x * naturalCanonicalFlux d g j x) ∂ν) =
          ∫ x, dualSource d g (dualBump k) x * (ψ x * naturalKatoForcing d g ε Dg x) ∂ν := by
      apply integral_congr_ae
      filter_upwards [actual_dualMass_eq_ae d g] with x hx
      dsimp only [dualSource, katoJointMultiplier, dualScalarMultiplier, naturalKatoForcing]
      rw [hx]
      ring
    exact hl.symm.trans (he.trans hr)
  have hlimit : (∫ x, naturalKatoWeakIntegrand d g Du ε ψ x ∂ν) =
      ∫ x, ψ x * naturalKatoForcing d g ε Dg x ∂ν := by
    have he := tendsto_nhds_unique (hA.2.add hError.2)
      (hB.2.congr fun k => (hEq k).symm)
    simpa only [add_zero] using he
  have hsplit : (∫ x, naturalKatoWeakIntegrand d g Du ε ψ x ∂ν) =
      (∫ x, ψ x * naturalKatoDensity d g Du ε x ∂ν) +
        ∑ a : Fin n, ∫ x, naturalKatoMetricFlux d g Du ε a x * coordinateDerivative ψ a x ∂ν := by
    change (∫ x, ψ x * naturalKatoDensity d g Du ε x +
      (∑ a : Fin n, naturalKatoMetricFlux d g Du ε a x * coordinateDerivative ψ a x) ∂ν) = _
    rw [integral_add hDI (integrable_finsetSum Finset.univ fun a _ => hFI a),
      integral_finsetSum Finset.univ fun a _ => hFI a]
  refine ⟨hFI, hDI, hBI, ?_⟩
  linarith only [hlimit, hsplit]

end KLSConstantImprovement.ActualRegularizedWeakBochner405
#print axioms KLSConstantImprovement.ActualRegularizedWeakBochner405.actual_regularized_weak_Bochner

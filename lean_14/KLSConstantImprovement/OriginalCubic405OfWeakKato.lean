import KLSConstantImprovement.ActualTargetCutoffKatoExcess405
import KLSConstantImprovement.ActualSoftTargetSourceHessianLimit405
import KLSConstantImprovement.ActualFixedSourcePolynomialMass405
import KLSConstantImprovement.OriginalCubic405MassSourceGate

/-! The complete original-law raw405 deduction from the ONE remaining
local analytic statement: actual weak Kato on the natural inverse. Source,
Hessian, inverse, forcing, cutoff, excess, mass and original-law passages
are all constructed internally. This module does not assert weak Kato. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped Topology ENNReal ContDiff BigOperators
namespace KLSConstantImprovement.OriginalCubic405OfWeakKato
open KLS ActualBoundedCanonicalSource ActualWeakKatoCompactExcess405 ActualTargetCutoffKatoExcess405
open ActualSoftTargetSourceHessianLimit405 ActualFixedSourcePolynomialMass405 ActualFixedSourceBoundedForcingMass405
open ActualCompactTargetExtensions405 ActualCenteredTargetForcing405 ActualSourcePullbackMetricGradient405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405 ActualCompactRawMetricGraph
open OriginalCubic405MassSourceGate
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def ActualNaturalWeakKatoGate405 : Prop :=
  ∀ {n : ℕ} {μ : Measure (Space n)} (d : SourceData μ) (hn : 1 ≤ n),
    admissibleMeasure μ →
    ∀ (g : Lp ℝ 2 (potentialMeasure d.potential)),
      (∫ x, g x ∂potentialMeasure d.potential) = 0 →
    ∀ (Dg : Fin n → Space n → ℝ),
      (∀ i, HasLocalWeakCoordinateDerivative (g : Space n → ℝ) (Dg i) i) →
      (∀ i, MemLp (Dg i) 2 (potentialMeasure d.potential)) →
    ∀ B : ℝ, 0 ≤ B →
      (∀ᵐ x ∂potentialMeasure d.potential,
        (∑ i : Fin n, rawCanonicalMetricDerivative d.potential Dg i x^2) ≤ B^2) →
    ∃ Dw : Fin n → Space n → ℝ,
      (∀ i E, IsCompact E → MemLp (Dw i) 2 (volume.restrict E)) ∧
      (∀ i, HasLocalWeakCoordinateDerivative
        (fun x => Real.sqrt (sourceVectorMass d.potential (naturalCanonicalFlux d g) x)) (Dw i) i) ∧
      ∀ ψ : Space n → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ → (∀ x, 0 ≤ ψ x) →
        (∑ i, ∫ x, rawKatoFlux d Dw i x * coordinateDerivative ψ i x ∂potentialMeasure d.potential) ≤
          ∫ x, (B-Real.sqrt (sourceVectorMass d.potential (naturalCanonicalFlux d g) x)/2)*ψ x
            ∂potentialMeasure d.potential

theorem mass_source_gate_of_actual_weak_Kato (hKato : ActualNaturalWeakKatoGate405) :
    BoundedStrongMassSourceGate405 := by
  intro n μ hn hμ hreg T h12 h23
  obtain ⟨d₀⟩ := exists_sourceData hμ hreg
  obtain ⟨idx, d, e, L, hidx, hadm, _heV, _heK, _heκ, hκ, hg0, hL, hg, hφ, hball, _hHs, hH⟩ :=
    exists_actual_softTarget_source_hessian_limit d₀ hn hμ
  have hc : 0 < d₀.targetConvexityConstant/9 := div_pos d₀.target_convexity_pos (by norm_num)
  have hMass (F : Space n → ℝ) (hF : ContDiff ℝ 1 F) (hcF : HasCompactSupport F) :
      ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂potentialMeasure e.potential,
        sourceVectorMass e.potential (naturalCanonicalFlux e (centeredTargetDatum e F hF.continuous)) x ≤ M := by
    apply fixed_source_centered_target_mass_bound_of_local_Kato d₀ hn hμ hidx d e hadm hc hκ hL hg0 hφ hg hH hball hF hcF
    intro k B hB hDg _hDgloc hΓ m hm
    have hDg2 (i : Fin n) : MemLp (pullbackRawGradient (d k) F i) 2 (potentialMeasure (d k).potential) :=
      (d k).pullback_weak_derivative_memLp hF i 2
    obtain ⟨Dw, hDw, hwDw, hweak⟩ := hKato (d k) hn (hadm k)
      (centeredTargetDatum (d k) F hF.continuous)
      (centeredTargetDatum_mean_zero (d k) F hF.continuous)
      (pullbackRawGradient (d k) F) hDg hDg2 B hB hΓ
    exact actual_target_pullback_excess_of_weak_sqrt_mass_Kato (d k) hn
      (centeredTargetDatum (d k) F hF.continuous)
      (centeredTargetDatum_mean_zero (d k) F hF.continuous) hB Dw hDw hwDw hweak
      (smoothCutoff_contDiff m) hm
  obtain ⟨CQ, CP, hCQ, hCP, hMQ, hMP⟩ :=
    fixed_source_quadratic_cubic_mass_of_bounded_forcing e hμ hMass T
  exact ⟨e, CQ, CP, hCQ, hCP, hMQ, hMP⟩

theorem original_literal_raw405_of_actual_weak_Kato (hKato : ActualNaturalWeakKatoGate405) :
    LiteralCubicVarianceObservationTransfer.UniversalLiteralCubicVarianceBound 405 :=
  original_literal_raw405_of_mass_source_gate (mass_source_gate_of_actual_weak_Kato hKato)

theorem original_observation_raw405_of_actual_weak_Kato (hKato : ActualNaturalWeakKatoGate405) :
    RawCubicWeightedBudget.UniversalRawCubicBound 405 :=
  original_observation_raw405_of_mass_source_gate (mass_source_gate_of_actual_weak_Kato hKato)

end KLSConstantImprovement.OriginalCubic405OfWeakKato
#print axioms KLSConstantImprovement.OriginalCubic405OfWeakKato.mass_source_gate_of_actual_weak_Kato
#print axioms KLSConstantImprovement.OriginalCubic405OfWeakKato.original_literal_raw405_of_actual_weak_Kato
#print axioms KLSConstantImprovement.OriginalCubic405OfWeakKato.original_observation_raw405_of_actual_weak_Kato

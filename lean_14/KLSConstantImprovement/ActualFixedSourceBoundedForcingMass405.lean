import KLSConstantImprovement.ActualCenteredTargetInverseDensityLimit405
import KLSConstantImprovement.ActualTargetCutoffErrorBudget405
import KLSConstantImprovement.ActualDensityMassFromLocalExcess405

/-! The actual fixed-source bounded-forcing application.  Every target,
source, inverse, derivative, cutoff domain, uniform cutoff-error budget and
limiting identification is paid.  The sole displayed analytic premise is
the literal compact local Kato excess estimate, to be discharged by the
separate local weak Gamma2 proof.  This conditional theorem does not assert
that estimate or unconditional mass boundedness. -/
noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ContDiff ENNReal BigOperators
namespace KLSConstantImprovement.ActualFixedSourceBoundedForcingMass405
open KLS ActualBoundedCanonicalSource ActualCompactTargetExtensions405
open ActualCenteredTargetInverseDensityLimit405 ActualTargetCutoffErrorBudget405
open ActualDensityMassFromLocalExcess405 ActualSoftTargetSourceLimit405
open ActualCenteredTargetForcing405 ActualGrowingTargetCutoffDomains405
open ActualTargetPullbackCutoffEnergy405 ActualSourcePullbackMetricGradient405
open ActualCompactRawMetricGraph ActualSignedCoordinateExcess405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem fixed_source_centered_target_mass_bound_of_local_Kato
    (d₀ : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    {idx : ℕ → ℕ} (hidx : StrictMono idx)
    (d : ∀ k, SourceData (whitenedSoftTargetMeasure d₀ (idx k))) (e : SourceData μ)
    (hadm : ∀ k, admissibleMeasure (whitenedSoftTargetMeasure d₀ (idx k)))
    {c L : ℝ} (hc : 0 < c) (hκ : ∀ k, c ≤ (d k).targetConvexityConstant)
    (hV : ∀ k p, L ≤ (d k).targetPotential p)
    (hg0 : ∀ k, gradient (d k).potential (0 : Space n) = 0)
    (hφ : ∀ x, Tendsto (fun k => (d k).potential x) atTop (𝓝 (e.potential x)))
    (hg : TendstoLocallyUniformly (fun k => gradient (d k).potential)
      (gradient e.potential) atTop)
    (hH : ∀ᵐ x ∂(volume : Measure (Space n)),
      Tendsto (fun k => coordinateHessian (d k).potential x) atTop
        (𝓝 (coordinateHessian e.potential x)))
    (hball : ∀ R : ℝ, ∀ᶠ k in atTop,
      closedBall (0 : Space n) R ⊆ interior (d k).targetSet)
    {F : Space n → ℝ} (hF : ContDiff ℝ 1 F) (hcF : HasCompactSupport F)
    (hKato : ∀ k (B : ℝ), 0 ≤ B →
      (∀ i, HasLocalWeakCoordinateDerivative
        (centeredTargetDatum (d k) F hF.continuous : Space n → ℝ)
        (pullbackRawGradient (d k) F i) i) →
      (∀ i E, IsCompact E → MemLp (pullbackRawGradient (d k) F i) 2 (volume.restrict E)) →
      (∀ᵐ x ∂potentialMeasure (d k).potential,
        (∑ i : Fin n, rawCanonicalMetricDerivative (d k).potential
          (pullbackRawGradient (d k) F) i x^2) ≤ B^2) →
      ∀ m : ℕ, HasCompactSupport (fun x => smoothCutoff n m (gradient (d k).potential x)) →
        Integrable (fun x => smoothCutoff n m (gradient (d k).potential x)^2 *
          naturalMassExcess (d k) (centeredTargetDatum (d k) F hF.continuous) (2*B) x^2)
            (potentialMeasure (d k).potential) ∧
        (∫ x, smoothCutoff n m (gradient (d k).potential x)^2 *
          naturalMassExcess (d k) (centeredTargetDatum (d k) F hF.continuous) (2*B) x^2
            ∂potentialMeasure (d k).potential) ≤
          4*(∫ x, sourceVectorMass (d k).potential
            (naturalCanonicalFlux (d k) (centeredTargetDatum (d k) F hF.continuous)) x *
              pullbackMetricSquare (d k) (smoothCutoff n m) x ∂potentialMeasure (d k).potential)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂potentialMeasure e.potential,
      sourceVectorMass e.potential (naturalCanonicalFlux e (centeredTargetDatum e F hF.continuous)) x ≤ M := by
  obtain ⟨C, hbF⟩ := hcF.exists_bound_of_continuous hF.continuous
  have hC : 0 ≤ C := (norm_nonneg (F 0)).trans (hbF 0)
  obtain ⟨G, hbG⟩ := (hasCompactSupport_gradient hcF).exists_bound_of_continuous
    (continuous_gradient_of_contDiff hF)
  have hG : 0 ≤ G := (norm_nonneg (gradient F 0)).trans (hbG 0)
  let S : ℝ := (16/c)*G^2
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  let B : ℝ := S+1
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hSB : S ≤ B^2 := by dsimp only [B]; nlinarith [sq_nonneg S]
  have hΓ (k : ℕ) : ∀ᵐ x ∂potentialMeasure (d k).potential,
      (∑ i : Fin n, rawCanonicalMetricDerivative (d k).potential
        (pullbackRawGradient (d k) F) i x^2) ≤ B^2 :=
    (centeredTargetDatum_metric_square_uniform (d k) hF hc (hκ k) hG hbG).mono
      fun _ hx => hx.trans hSB
  obtain ⟨W, σ, hσ, _hW, _hfield, hw, hid⟩ :=
    exists_actual_centered_target_inverse_density_limit d₀ hn hμ hidx d e hc hκ hV hg0 hφ
      (fun x => hg.tendstoLocallyUniformlyOn.tendsto_at (mem_univ x)) hH hF hC hbF
  obtain ⟨K, _hK, herror⟩ := actual_centered_target_family_cutoff_error_budget d hn hc hκ
    hF.continuous hC hbF
  have hgs : TendstoLocallyUniformly (fun k => gradient (d (σ k)).potential)
      (gradient e.potential) atTop := by
    intro u hu x
    obtain ⟨E, hE, hev⟩ := hg u hu x
    exact ⟨E, hE, hσ.tendsto_atTop.eventually hev⟩
  have hexcess (m : ℕ) : ∀ᶠ k in atTop,
      Integrable (fun x => smoothCutoff n m (gradient (d (σ k)).potential x)^2 *
        naturalMassExcess (d (σ k)) (centeredTargetDatum (d (σ k)) F hF.continuous) (2*B) x^2)
          (potentialMeasure (d (σ k)).potential) ∧
      (∫ x, smoothCutoff n m (gradient (d (σ k)).potential x)^2 *
        naturalMassExcess (d (σ k)) (centeredTargetDatum (d (σ k)) F hF.continuous) (2*B) x^2
          ∂potentialMeasure (d (σ k)).potential) ≤
            (4*(16/c)*K^2*C^2)*(cutoffScale m)^2 := by
    have hcompact := actual_target_pullback_eventually_compact d hadm hball
      (smoothCutoff_hasCompactSupport m)
    filter_upwards [hσ.tendsto_atTop.eventually hcompact] with k hk
    have he := hKato (σ k) B hB
      (centeredTargetDatum_hasLocalWeakCoordinateDerivative (d (σ k)) hF)
      (centeredTargetDatum_derivative_domains (d (σ k)) hF).1 (hΓ (σ k)) m hk
    refine ⟨he.1, he.2.trans ?_⟩
    calc
      _ ≤ 4*((16/c)*K^2*C^2*(cutoffScale m)^2) :=
        mul_le_mul_of_nonneg_left (herror m (σ k)).2 (by norm_num)
      _ = _ := by ring
  refine ⟨n*(2*B)^2, mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _), ?_⟩
  exact actual_density_limit_mass_bound_of_local_excess (fun k => d (σ k)) e
    (fun k => centeredTargetDatum (d (σ k)) F hF.continuous)
    (centeredTargetDatum e F hF.continuous) (fun k => hg0 (σ k))
    (fun x => (hφ x).comp hσ.tendsto_atTop) hgs W hw hid
    (mul_nonneg (by norm_num) hB) hexcess

end KLSConstantImprovement.ActualFixedSourceBoundedForcingMass405
#print axioms KLSConstantImprovement.ActualFixedSourceBoundedForcingMass405.fixed_source_centered_target_mass_bound_of_local_Kato

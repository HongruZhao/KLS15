import KLSConstantImprovement.ActualDensityPoissonLimit405
import KLSConstantImprovement.ActualSoftTargetForcingRhs405

/-! For each fixed bounded C1 extension, a further weak inverse-field
subsequence converges to the actual canonical inverse on the SAME fixed
original source. Only the inverse subsequence and Hilbert limit depend on
the extension; the original source and the given soft family do not change.
The raw derivative, Poisson equation and forcing RHS limits are proved by
their actual source-family passage theorems. -/
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ContDiff ENNReal BigOperators
namespace KLSConstantImprovement.ActualCenteredTargetInverseDensityLimit405
open KLS ActualBoundedCanonicalSource ActualCompactTargetExtensions405
open ActualDensityInverseWeakCompactness405 ActualDensityWeightedL2405
open ActualDensityPoissonLimit405 ActualSoftTargetForcingRhs405
open ActualSoftTargetSourceLimit405 ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricInverse
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem exists_actual_centered_target_inverse_density_limit
    (d₀ : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    {idx : ℕ → ℕ} (hidx : StrictMono idx)
    (d : ∀ k, SourceData (whitenedSoftTargetMeasure d₀ (idx k))) (e : SourceData μ)
    {c L : ℝ} (hc : 0 < c) (hκ : ∀ k, c ≤ (d k).targetConvexityConstant)
    (hV : ∀ k p, L ≤ (d k).targetPotential p)
    (hg0 : ∀ k, gradient (d k).potential (0 : Space n) = 0)
    (hφ : ∀ x, Tendsto (fun k => (d k).potential x) atTop (𝓝 (e.potential x)))
    (hg : ∀ x, Tendsto (fun k => gradient (d k).potential x) atTop
      (𝓝 (gradient e.potential x)))
    (hH : ∀ᵐ x ∂(volume : Measure (Space n)),
      Tendsto (fun k => coordinateHessian (d k).potential x) atTop
        (𝓝 (coordinateHessian e.potential x)))
    {F : Space n → ℝ} (hF : ContDiff ℝ 1 F) {C : ℝ}
    (hC : 0 ≤ C) (hbF : ∀ y, ‖F y‖ ≤ C) :
    ∃ (W : DensityInverseAmbient n) (σ : ℕ → ℕ), StrictMono σ ∧ ‖W‖ ≤ 2*C ∧
      (∀ k, ‖actualDensityInverseField (d (σ k))
        (centeredTargetDatum (d (σ k)) F hF.continuous)‖ ≤ 2*C) ∧
      (∀ Y : DensityInverseAmbient n,
        Tendsto (fun k => inner ℝ (actualDensityInverseField (d (σ k))
          (centeredTargetDatum (d (σ k)) F hF.continuous)) Y) atTop (𝓝 (inner ℝ W Y))) ∧
      (∀ i, (canonicalMetricGradient e.potential i
        (sourceMetricInverseH1 e (centeredTargetDatum e F hF.continuous)) : Space n → ℝ)
        =ᵐ[potentialMeasure e.potential]
          (fromVolumeL2 e.source_C1.continuous (W i.succ) : Space n → ℝ)) := by
  let g (k : ℕ) := centeredTargetDatum (d k) F hF.continuous
  have hnorm (k : ℕ) : ‖g k‖ ≤ C :=
    centeredTargetDatum_norm_le (d k) F hF.continuous hC hbF
  obtain ⟨W, σ, hσ, hW, hw⟩ := exists_actual_densityInverse_weak_subsequence d g hC hnorm
  have hfield (k : ℕ) : ‖actualDensityInverseField (d k) (g k)‖ ≤ 2*C := by
    have hh := actualDensityInverseField_norm_sq (d k) (g k)
    have hs := (sq_le_sq₀ (norm_nonneg (g k)) hC).mpr (hnorm k)
    nlinarith [norm_nonneg (actualDensityInverseField (d k) (g k))]
  have hφs (x : Space n) : Tendsto (fun k => (d (σ k)).potential x) atTop
      (𝓝 (e.potential x)) := (hφ x).comp hσ.tendsto_atTop
  have hgs (x : Space n) : Tendsto (fun k => gradient (d (σ k)).potential x) atTop
      (𝓝 (gradient e.potential x)) := (hg x).comp hσ.tendsto_atTop
  have hHs : ∀ᵐ x ∂(volume : Measure (Space n)),
      Tendsto (fun k => coordinateHessian (d (σ k)).potential x) atTop
        (𝓝 (coordinateHessian e.potential x)) := hH.mono fun x hx => hx.comp hσ.tendsto_atTop
  have hrhs (ψ : Space n → ℝ) (hψ : ContDiff ℝ 3 ψ) (hcψ : HasCompactSupport ψ) :
      Tendsto (fun k => ∫ x, g (σ k) x*ψ x ∂potentialMeasure (d (σ k)).potential) atTop
        (𝓝 (∫ x, centeredTargetDatum e F hF.continuous x*ψ x ∂potentialMeasure e.potential)) :=
    actual_softTarget_centered_compact_rhs_tendsto d₀ hμ (hidx.comp hσ)
      (fun k => d (σ k)) e (fun k => hg0 (σ k)) hφs hgs
      hF.continuous hC hbF hψ.continuous hcψ
  have hid := actual_density_limit_metric_gradient_identification (fun k => d (σ k)) e hn
    (fun k => g (σ k)) (fun k => centeredTargetDatum_mean_zero (d (σ k)) F hF.continuous)
    (centeredTargetDatum e F hF.continuous) (centeredTargetDatum_mean_zero e F hF.continuous)
    W hc (fun k => hκ (σ k)) (fun k p => hV (σ k) p) (fun k => hg0 (σ k))
    hφs hHs (fun k => hfield (σ k)) hw hrhs
  exact ⟨W, σ, hσ, hW, (fun k => hfield (σ k)), hw, hid⟩

end KLSConstantImprovement.ActualCenteredTargetInverseDensityLimit405
#print axioms KLSConstantImprovement.ActualCenteredTargetInverseDensityLimit405.exists_actual_centered_target_inverse_density_limit

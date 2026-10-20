import KLSConstantImprovement.ActualAdmissibleSoftSourceLimit405
import KLSConstantImprovement.ActualSourceHessianAELimit405

/-! Actual smooth convex soft-target approximants, their centered genuine
SourceData, and one limiting SourceData for the original bounded law, now
with identified strong local and AE Hessian convergence on the same family.
No source uniqueness, classical regularity upgrade or inverse mass bound
is asserted. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ContDiff ENNReal
namespace KLSConstantImprovement.ActualSoftTargetSourceHessianLimit405
open KLS ActualBoundedCanonicalSource ActualAdmissibleSoftSourceLimit405
open ActualSoftTargetWhitening405 ActualSoftTargetSourceLimit405 ActualSourceHessianAELimit405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem exists_actual_softTarget_source_hessian_limit
    (d₀ : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ) :
    ∃ (idx : ℕ → ℕ) (d : ∀ k, SourceData (whitenedSoftTargetMeasure d₀ (idx k)))
      (e : SourceData μ) (L : ℝ),
      StrictMono idx ∧
      (∀ k, admissibleMeasure (whitenedSoftTargetMeasure d₀ (idx k))) ∧
      e.targetPotential = d₀.targetPotential ∧ e.targetSet = d₀.targetSet ∧
      e.targetConvexityConstant = d₀.targetConvexityConstant ∧
      (∀ k, d₀.targetConvexityConstant/9 ≤ (d k).targetConvexityConstant) ∧
      (∀ k, gradient (d k).potential (0 : Space n) = 0) ∧
      (∀ k p, L ≤ (d k).targetPotential p) ∧
      TendstoLocallyUniformly (fun k => gradient (d k).potential) (gradient e.potential) atTop ∧
      (∀ x, Tendsto (fun k => (d k).potential x) atTop (𝓝 (e.potential x))) ∧
      (∀ R : ℝ, ∀ᶠ k in atTop, closedBall (0 : Space n) R ⊆ interior (d k).targetSet) ∧
      (∀ (E : Set (Space n)), IsCompact E → ∀ a b, Tendsto (fun k => eLpNorm
        (fun x => coordinateHessian (d k).potential x a b-
          coordinateHessian e.potential x a b) 2 (volume.restrict E)) atTop (𝓝 0)) ∧
      (∀ᵐ x ∂(volume : Measure (Space n)),
        Tendsto (fun k => coordinateHessian (d k).potential x) atTop
          (𝓝 (coordinateHessian e.potential x))) := by
  obtain ⟨idx, d, e, L, hidx, hadm, heV, heK, heκ, hκ, hg0, hL, hg, hp, hball⟩ :=
    exists_admissible_centered_softTarget_sourceData_limit d₀ hn hμ
  have hgp (x : Space n) : Tendsto (fun k => gradient (d k).potential x) atTop
      (𝓝 (gradient e.potential x)) :=
    hg.tendstoLocallyUniformlyOn.tendsto_at (mem_univ x)
  obtain ⟨σ, hσ, hHs, hHa⟩ := exists_actual_hessian_strong_local_ae_subsequence
    d e (fun k => (hadm k).isotropic)
      (div_pos d₀.target_convexity_pos (by norm_num : (0 : ℝ) < 9)) hκ hg0 (hp 0) hgp
  refine ⟨fun k => idx (σ k), fun k => d (σ k), e, L, hidx.comp hσ,
    (fun k => hadm (σ k)), heV, heK, heκ, (fun k => hκ (σ k)),
    (fun k => hg0 (σ k)), (fun k p => hL (σ k) p), ?_,
    (fun x => (hp x).comp hσ.tendsto_atTop), ?_, hHs, hHa⟩
  · intro u hu x
    obtain ⟨E, hE, hev⟩ := hg u hu x
    exact ⟨E, hE, hσ.tendsto_atTop.eventually hev⟩
  · intro R
    exact hσ.tendsto_atTop.eventually (hball R)

end KLSConstantImprovement.ActualSoftTargetSourceHessianLimit405
#print axioms KLSConstantImprovement.ActualSoftTargetSourceHessianLimit405.exists_actual_softTarget_source_hessian_limit

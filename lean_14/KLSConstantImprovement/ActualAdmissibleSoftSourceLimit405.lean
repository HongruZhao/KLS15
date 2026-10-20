import KLSConstantImprovement.ActualSoftTargetSourceLimit405

/-! The final actual soft-target family with probability/admissibility and
isotropy exposed for EVERY member.  A proved late-tail restriction preserves
the same original source limit and all common geometric bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology NNReal ContDiff ENNReal
namespace KLSConstantImprovement.ActualAdmissibleSoftSourceLimit405
open KLS ActualBoundedCanonicalSource ActualSoftTargetSourceLimit405
open ActualSoftTargetWhitening405 ActualInteriorCapConfinement405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem exists_admissible_centered_softTarget_sourceData_limit
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
      (∀ R : ℝ, ∀ᶠ k in atTop, closedBall (0 : Space n) R ⊆ interior (d k).targetSet) := by
  obtain ⟨idx, d, e, L, hidx, heV, heK, heκ, hκ, hg0, hLo, hg, hp, hball⟩ :=
    exists_centered_softTarget_sourceData_limit d₀ hn hμ
  have hne : d₀.targetSet.Nonempty := by
    obtain ⟨r, hr, hb⟩ := actual_target_contains_origin_ball d₀
    exact ⟨0, hb (mem_ball_self hr)⟩
  have hev : ∀ᶠ j in atTop, admissibleMeasure (whitenedSoftTargetMeasure d₀ j) := by
    exact (softTarget_whitening_eventual hμ d₀.target_smooth d₀.target_convexity_pos
      (strongConvexOn_iff_convex.mpr d₀.target_strong) d₀.target_closed hne d₀.target_convex
        d₀.target_representation).mono fun _ hj => hj.1
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hidx.tendsto_atTop.eventually hev)
  let t : ℕ → ℕ := fun k => N+k
  have ht : StrictMono t := fun i j hij => Nat.add_lt_add_left hij N
  refine ⟨fun k => idx (t k), fun k => d (t k), e, L, hidx.comp ht,
    (fun k => hN (N+k) (Nat.le_add_right N k)), heV, heK, heκ,
    (fun k => hκ (t k)), (fun k => hg0 (t k)), (fun k p => hLo (t k) p), ?_, ?_, ?_⟩
  · intro u hu x
    obtain ⟨E, hE, he⟩ := hg u hu x
    exact ⟨E, hE, ht.tendsto_atTop.eventually he⟩
  · intro x
    exact (hp x).comp ht.tendsto_atTop
  · intro R
    exact ht.tendsto_atTop.eventually (hball R)

end KLSConstantImprovement.ActualAdmissibleSoftSourceLimit405
#print axioms KLSConstantImprovement.ActualAdmissibleSoftSourceLimit405.exists_admissible_centered_softTarget_sourceData_limit

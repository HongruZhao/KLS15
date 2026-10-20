import KLSConstantImprovement.ActualSoftTargetSource405
import KLSConstantImprovement.ActualSoftTargetLowerBound405
import KLSConstantImprovement.ActualGrowingAffineTargets405
import KLSConstantImprovement.ActualCenteredSourceLimit405

/-! The actual direct-to-original bounded source approximation.  All laws,
normalizations, whitening matrices, centered sources and weak geometric limit
are constructed.  Poisson/inverse/flux limits and the local excess estimate
are deliberately separate remaining analytic work. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Matrix Metric
open scoped Topology NNReal ContDiff ENNReal
namespace KLSConstantImprovement.ActualSoftTargetSourceLimit405
open KLS ActualBoundedCanonicalSource ActualSourceCentering405 ActualCenteredSourceData405
open ActualSoftTargetIntegrals405 ActualStrongPotentialMoments405 ActualSoftTargetNormalization405
open ActualSoftTargetWhitening405 ActualSoftTargetSource405 ActualSoftTargetLowerBound405
open ActualGrowingAffineTargets405 ActualCenteredSourceLimit405 ActualInteriorCapConfinement405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

def whitenedSoftTargetMeasure (d : SourceData μ) (j : ℕ) : Measure (Space n) :=
  whitenedMeasure (softTargetMeasure d.targetPotential d.targetSet j)

theorem exists_centered_softTarget_sourceData_limit
    (d₀ : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ) :
    ∃ (idx : ℕ → ℕ) (d : ∀ k, SourceData (whitenedSoftTargetMeasure d₀ (idx k)))
      (e : SourceData μ) (L : ℝ),
      StrictMono idx ∧
      e.targetPotential = d₀.targetPotential ∧ e.targetSet = d₀.targetSet ∧
      e.targetConvexityConstant = d₀.targetConvexityConstant ∧
      (∀ k, d₀.targetConvexityConstant/9 ≤ (d k).targetConvexityConstant) ∧
      (∀ k, gradient (d k).potential (0 : Space n) = 0) ∧
      (∀ k p, L ≤ (d k).targetPotential p) ∧
      TendstoLocallyUniformly (fun k => gradient (d k).potential) (gradient e.potential) atTop ∧
      (∀ x, Tendsto (fun k => (d k).potential x) atTop (𝓝 (e.potential x))) ∧
      (∀ R : ℝ, ∀ᶠ k in atTop, closedBall (0 : Space n) R ⊆ interior (d k).targetSet) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  let V := d₀.targetPotential
  let K := d₀.targetSet
  let κ := d₀.targetConvexityConstant
  have hV : ContDiff ℝ (⊤ : ℕ∞) V := d₀.target_smooth
  have hκ : 0 < κ := d₀.target_convexity_pos
  have hs : StrongConvexOn univ κ V := strongConvexOn_iff_convex.mpr d₀.target_strong
  have hK : IsClosed K := d₀.target_closed
  have hc : Convex ℝ K := d₀.target_convex
  have hne : K.Nonempty := by
    obtain ⟨r, hr, hb⟩ := actual_target_contains_origin_ball d₀
    exact ⟨0, hb (mem_ball_self hr)⟩
  have heq : μ = (potentialMeasure V).restrict K := d₀.target_representation
  letI := strongPotential_isFiniteMeasure (hV.of_le (by simp)) hκ hs
  letI : ∀ j, IsProbabilityMeasure (softTargetMeasure V K j) :=
    fun j => softTargetMeasure_probability hV.continuous.measurable K j
  obtain ⟨L, hLo⟩ := eventually_softTarget_affine_potential_lower hμ hV hκ hs hK hne hc heq
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((eventually_softTarget_sources_uniform_convexity hμ hV hκ hs hK hne hc heq).and hLo)
  choose hA D hpot hset hconst hconv using fun k : ℕ =>
    (hN (N+k) (Nat.le_add_right N k)).1
  let ρ : ℕ → Measure (Space n) := fun k => whitenedMeasure (softTargetMeasure V K (N+k))
  have hDκ (k : ℕ) : κ/9 ≤ (D k).targetConvexityConstant := hconv k
  have hDLo (k : ℕ) (p : Space n) : L ≤ (D k).targetPotential p := by
    rw [hpot k]
    exact (hN (N+k) (Nat.le_add_right N k)).2 (hA k) p
  have hshift : StrictMono (fun k : ℕ => N+k) := fun i j hij => Nat.add_lt_add_left hij N
  have hweak (v : Space n → ℝ) (hv : Continuous v) (B : ℝ) (hb : ∀ x, ‖v x‖ ≤ B) :
      Tendsto (fun k => ∫ y, v y ∂ρ k) atTop (𝓝 (∫ y, v y ∂μ)) :=
    (tendsto_integral_bounded_whitened_softTarget hμ hV hκ hs hK hne hc heq hv hb).comp hshift.tendsto_atTop
  obtain ⟨s, e, hsmono, heV, heK, heκ, hg, hp⟩ := exists_centered_sourceData_subseq_limit
    d₀ hn D (div_pos hκ (by norm_num) : 0 < κ/9) hDκ hweak
  let idx : ℕ → ℕ := fun k => N+s k
  have hidx : StrictMono idx := hshift.comp hsmono
  let ds : ∀ k, SourceData (whitenedSoftTargetMeasure d₀ (idx k)) :=
    fun k => centeredCanonicalSource (D (s k))
  refine ⟨idx, ds, e, L, hidx, heV, heK, heκ, ?_, ?_, ?_, hg, hp, ?_⟩
  · intro k
    change κ/9 ≤ (centeredCanonicalSource (D (s k))).targetConvexityConstant
    rw [(centeredCanonicalSource_target (D (s k))).2.2]
    exact hDκ (s k)
  · intro k
    exact centeredCanonicalSource_gradient_zero (D (s k))
  · intro k p
    change L ≤ (centeredCanonicalSource (D (s k))).targetPotential p
    rw [(centeredCanonicalSource_target (D (s k))).1]
    exact hDLo (s k) p
  · intro R
    have hev := eventually_fixed_ball_interior_growing_affine
      (softTarget_whitening_coefficients hμ hV hκ hs hK hne hc heq) R
    filter_upwards [hidx.tendsto_atTop.eventually hev] with k hk
    change closedBall (0 : Space n) R ⊆ interior (centeredCanonicalSource (D (s k))).targetSet
    rw [(centeredCanonicalSource_target (D (s k))).2.1, hset (s k)]
    exact hk (hA (s k))

end KLSConstantImprovement.ActualSoftTargetSourceLimit405
#print axioms KLSConstantImprovement.ActualSoftTargetSourceLimit405.exists_centered_softTarget_sourceData_limit

import KLSConstantImprovement.ActualDualCapCoercivity405
import KLSConstantImprovement.ActualSourceCentering405
import KLS.MomentGradientHomeomorph

/-! A single uniform linear cone for sources whose targets converge to an
original bounded admissible law. Only small caps inside that actual target
are needed; full support of the limiting target is not assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric InnerProductSpace
open scoped Topology BigOperators ENNReal NNReal
namespace KLSConstantImprovement.ActualInteriorCapConfinement405
open KLS ActualDualCapCoercivity405 ActualBoundedCanonicalSource ActualSourceCentering405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_target_contains_origin_ball (d : SourceData μ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ball (0 : Space n) ρ ⊆ d.targetSet := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hzero : gradient d.potential (actualSourceMinimum d) = 0 := by
    have hg := centeredSourcePotential_gradient_zero d
    simpa only [centeredSourcePotential, gradient_normalizeAt, zero_add] using hg
  have hi := moment_gradient_mem_interior_domain d.source_lipschitz d.source_convex
    d.target_smooth.continuous d.target_closed d.target_convex
    (d.pushforward.trans d.target_representation) (actualSourceMinimum d)
  rw [hzero] at hi
  have hs := momentLegendreDomain_subset_closedTarget d.source_lipschitz d.source_convex
    d.target_closed d.target_convex (d.pushforward.trans d.target_representation)
  have h0 : (0 : Space n) ∈ interior d.targetSet := interior_mono hs hi
  exact Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)

theorem scaled_axis_caps_separate (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) (x : Space n) :
    ∃ i : Fin n × Bool, ∀ p ∈ ball (r • axisCapCenter (n := n) 1 i) r,
      r * ‖x‖ ≤ inner ℝ p x := by
  obtain ⟨i, hi⟩ := axis_caps_separate hn (show (0 : ℝ) ≤ 1 by norm_num) x
  refine ⟨i, fun p hp => ?_⟩
  have he : r⁻¹ • p - axisCapCenter (n := n) 1 i =
      r⁻¹ • (p - r • axisCapCenter (n := n) 1 i) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have hq : r⁻¹ • p ∈ ball (axisCapCenter (n := n) 1 i) 1 := by
    rw [mem_ball_iff_norm, he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    have hh := mul_lt_mul_of_pos_left (mem_ball_iff_norm.mp hp) (inv_pos.mpr hr)
    simpa only [inv_mul_cancel₀ hr.ne'] using hh
  have hh := mul_le_mul_of_nonneg_left (hi _ hq) hr.le
  simp only [inner_smul_left, starRingEnd_apply, star_trivial, one_mul] at hh
  rwa [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at hh

theorem actual_positive_axis_caps (d : SourceData μ) :
    ∃ r : ℝ, 0 < r ∧ ∀ i : Fin n × Bool,
      0 < μ (ball (r • axisCapCenter (n := n) 1 i) r) := by
  obtain ⟨ρ, hρ, hball⟩ := actual_target_contains_origin_ball d
  let r := ρ / (4 * ((n : ℝ) + 1))
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨r, hr, fun i => ?_⟩
  have hc : ‖r • axisCapCenter (n := n) 1 i‖ = 2 * n * r := by
    rcases i with ⟨i, b⟩
    cases b <;> simp [axisCapCenter, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hr.le, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ n by positivity)] <;> ring
  have hrr : r * (4 * ((n : ℝ) + 1)) = ρ := by dsimp [r]; field_simp
  have hsub : ball (r • axisCapCenter (n := n) 1 i) r ⊆ d.targetSet := by
    intro p hp
    apply hball
    rw [mem_ball, dist_zero_right]
    have hh := norm_le_norm_sub_add p (r • axisCapCenter (n := n) 1 i)
    have hdist := mem_ball_iff_norm.mp hp
    rw [hc] at hh
    nlinarith
  rw [d.target_representation, Measure.restrict_apply measurableSet_ball, inter_eq_left.mpr hsub]
  apply pos_iff_ne_zero.mpr
  intro hz
  have hv := volume_absolutelyContinuous_potentialMeasure_of_measurable
    d.target_smooth.continuous.measurable hz
  exact (measure_ball_pos volume _ hr).ne' hv

theorem actual_bounded_target_limit_uniform_cone (d : SourceData μ) (hn : 1 ≤ n)
    [IsProbabilityMeasure μ] {ν : ℕ → Measure (Space n)}
    [∀ k, IsProbabilityMeasure (ν k)] {f : ℕ → Space n → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hE : ∀ k, momentDualEnergy (ν k) (f k) ≤ ENNReal.ofReal K)
    (hlim : ∀ v : Space n → ℝ, Continuous v → HasCompactSupport v →
      Tendsto (fun k => ∫ p, v p ∂ν k) atTop (𝓝 (∫ p, v p ∂μ))) :
    ∃ r B : ℝ, 0 < r ∧ 0 ≤ B ∧ ∀ᶠ k in atTop, ∀ x, r * ‖x‖ - B ≤ f k x := by
  obtain ⟨r, hr, hcaps⟩ := actual_positive_axis_caps d
  let b (i : Fin n × Bool) : ContDiffBump (r • axisCapCenter (n := n) 1 i) :=
    ⟨r / 2, r, by positivity, by linarith⟩
  let β (i : Fin n × Bool) : Space n → ℝ := b i
  have hi (i : Fin n × Bool) : Integrable (β i) μ :=
    (b i).continuous.integrable_of_hasCompactSupport (b i).hasCompactSupport
  have hp (i : Fin n × Bool) : 0 < ∫ p, β i p ∂μ := by
    rw [integral_pos_iff_support_of_nonneg (fun p => (b i).nonneg) (hi i)]
    simpa only [β, ContDiffBump.support_eq] using hcaps i
  let e (i : Fin n × Bool) := (∫ p, β i p ∂μ) / 2
  obtain ⟨m, hm, hb⟩ := (Set.finite_range e).isCompact.exists_forall_le'
    continuous_id.continuousOn (a := 0) (by
      rintro y ⟨i, rfl⟩
      exact half_pos (hp i))
  have hmass : ∀ᶠ k in atTop, ∀ i, m ≤ ∫ p, β i p ∂ν k := by
    apply Filter.eventually_all.mpr
    intro i
    have he : e i < ∫ p, β i p ∂μ := half_lt_self (hp i)
    filter_upwards [(tendsto_order.1
      (hlim (β i) (b i).continuous (b i).hasCompactSupport)).1 (e i) he] with k hk
    exact (hb _ (mem_range_self i)).trans hk.le
  refine ⟨r, K / m, hr, div_nonneg hK hm.le, ?_⟩
  filter_upwards [hmass] with k hk x
  obtain ⟨i, hsep⟩ := scaled_axis_caps_separate hn hr x
  apply dual_cap_barrier hK hm (hE k)
    ((b i).continuous.integrable_of_hasCompactSupport (b i).hasCompactSupport)
    (fun p => (b i).nonneg) (fun p => (b i).le_one) (hk i) x
  intro p hp
  apply hsep p
  have hmem : p ∈ Function.support (b i) := hp
  rwa [(b i).support_eq] at hmem

end KLSConstantImprovement.ActualInteriorCapConfinement405
#print axioms KLSConstantImprovement.ActualInteriorCapConfinement405.actual_target_contains_origin_ball
#print axioms KLSConstantImprovement.ActualInteriorCapConfinement405.scaled_axis_caps_separate
#print axioms KLSConstantImprovement.ActualInteriorCapConfinement405.actual_positive_axis_caps
#print axioms KLSConstantImprovement.ActualInteriorCapConfinement405.actual_bounded_target_limit_uniform_cone

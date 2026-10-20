import KLSConstantImprovement.ActualSourceFamilyRootPassage405
import KLSConstantImprovement.ActualDensityWeakScalarPair405
import Mathlib.Topology.Order.LiminfLimsup

/-! The actual varying raw-gradient test coefficients converge strongly
in the fixed Lebesgue L2 ambient.  Their bounds use the common source
potential bound and the actual target convexity modulus. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
namespace KLSConstantImprovement.ActualDensityGradientCoefficient405
open KLS ActualBoundedCanonicalSource ActualSourceFamilyRootPassage405
open ActualDensityWeightedL2405 ActualBoundedCoefficientL2Passage405
open ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricOrdinaryGraph
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {ν : ℕ → Measure (Space n)} {μ : Measure (Space n)}

theorem actual_centered_family_global_potential_lower (d : ∀ k, SourceData (ν k))
    (hg : ∀ k, gradient (d k).potential 0 = 0) {z : ℝ}
    (hz : Tendsto (fun k => (d k).potential 0) atTop (𝓝 z)) :
    ∃ A : ℝ, ∀ k x, A ≤ (d k).potential x := by
  obtain ⟨A, hA⟩ := hz.bddBelow_range
  refine ⟨A, fun k x => (hA (mem_range_self k)).trans ?_⟩
  have h := gradient_mem_convexSubgradient (d k).source_convex
    ((d k).source_C1.differentiable (by norm_num) (0 : Space n))
  have hh := h x
  simpa only [hg k, inner_zero_left, add_zero] using hh

def densityGradientCoefficient (d : SourceData μ) (E : Set (Space n))
    (i a : Fin n) : Space n → ℝ :=
  E.indicator (fun x => canonicalMetricUnroot d.potential x i a * inverseDensityHalf d.potential x)

theorem density_gradient_coefficient_mul_tendsto_L2
    (d : ∀ k, SourceData (ν k)) (d₀ : SourceData μ)
    {κ P : ℝ} (hκ : 0 < κ) (hk : ∀ k, κ ≤ (d k).targetConvexityConstant)
    (hφ : ∀ x, Tendsto (fun k => (d k).potential x) atTop (𝓝 (d₀.potential x)))
    (hH : ∀ᵐ x ∂(volume : Measure (Space n)), Tendsto
      (fun k => coordinateHessian (d k).potential x) atTop (𝓝 (coordinateHessian d₀.potential x)))
    {E : Set (Space n)} (hE : IsCompact E)
    (hp : ∀ k x, x ∈ E → (d k).potential x ≤ P)
    (i a : Fin n) {f : Space n → ℝ} (hf : MemLp f 2 (volume : Measure (Space n))) :
    ∃ (ha : ∀ k, MemLp (fun x => densityGradientCoefficient (d k) E i a x * f x) 2 volume)
      (hb : MemLp (fun x => densityGradientCoefficient d₀ E i a x * f x) 2 volume),
      Tendsto (fun k => (ha k).toLp (fun x => densityGradientCoefficient (d k) E i a x * f x))
        atTop (𝓝 (hb.toLp (fun x => densityGradientCoefficient d₀ E i a x * f x))) := by
  let B : ℝ := (16/κ+1)*Real.exp (P/2)
  have hBn : 0 ≤ B := by dsimp only [B]; positivity
  have hmeas (s : SourceData μ) : AEStronglyMeasurable
      (densityGradientCoefficient s E i a) (volume : Measure (Space n)) := by
    have hS := (sourceMetricUnroot_aestronglyMeasurable s).mono_ac
      (volume_absolutelyContinuous_potentialMeasure s.source_C1.continuous)
    have hentry := (continuous_apply a).comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable hS)
    have hρ : Continuous (inverseDensityHalf s.potential) :=
      Real.continuous_exp.comp (s.source_C1.continuous.div_const 2)
    exact (hentry.mul hρ.aestronglyMeasurable).indicator hE.measurableSet
  have hm (k : ℕ) : AEStronglyMeasurable (densityGradientCoefficient (d k) E i a)
      (volume : Measure (Space n)) := by
    have hS := (sourceMetricUnroot_aestronglyMeasurable (d k)).mono_ac
      (volume_absolutelyContinuous_potentialMeasure (d k).source_C1.continuous)
    have hentry := (continuous_apply a).comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable hS)
    have hρ : Continuous (inverseDensityHalf (d k).potential) :=
      Real.continuous_exp.comp ((d k).source_C1.continuous.div_const 2)
    exact (hentry.mul hρ.aestronglyMeasurable).indicator hE.measurableSet
  have hb (k : ℕ) : ∀ᵐ x ∂(volume : Measure (Space n)),
      ‖densityGradientCoefficient (d k) E i a x‖ ≤ B := by
    filter_upwards [actual_family_unroot_uniform_entry_bound d hκ hk k i a] with x hx
    by_cases hxE : x ∈ E
    · rw [densityGradientCoefficient, indicator_of_mem hxE, norm_mul]
      have hρ : ‖inverseDensityHalf (d k).potential x‖ ≤ Real.exp (P/2) := by
        rw [inverseDensityHalf, Real.norm_of_nonneg (Real.exp_nonneg _)]
        exact Real.exp_le_exp.mpr (by linarith [hp k x hxE])
      exact mul_le_mul hx hρ (norm_nonneg _) (by positivity)
    · rw [densityGradientCoefficient, indicator_of_notMem hxE, norm_zero]
      exact hBn
  have ht : ∀ᵐ x ∂(volume : Measure (Space n)), Tendsto
      (fun k => densityGradientCoefficient (d k) E i a x) atTop
      (𝓝 (densityGradientCoefficient d₀ E i a x)) := by
    filter_upwards [actual_family_roots_tendsto_ae d d₀ hH] with x hx
    by_cases hxE : x ∈ E
    · have hS := (((continuous_apply a).comp (continuous_apply i)).continuousAt.tendsto.comp hx.2)
      have hρ := (Real.continuous_exp.tendsto _).comp ((hφ x).div_const 2)
      simpa only [densityGradientCoefficient, indicator_of_mem hxE, inverseDensityHalf,
        Function.comp_def] using hS.mul hρ
    · simp only [densityGradientCoefficient, indicator_of_notMem hxE]
      exact tendsto_const_nhds
  have hb₀ : ∀ᵐ x ∂(volume : Measure (Space n)), ‖densityGradientCoefficient d₀ E i a x‖ ≤ B := by
    filter_upwards [ht, ae_all_iff.mpr hb] with x hx hy
    exact le_of_tendsto hx.norm (Eventually.of_forall hy)
  exact bounded_coefficient_mul_tendsto_L2 hm (hmeas d₀) hBn hb hb₀ ht hf

end KLSConstantImprovement.ActualDensityGradientCoefficient405
#print axioms KLSConstantImprovement.ActualDensityGradientCoefficient405.actual_centered_family_global_potential_lower
#print axioms KLSConstantImprovement.ActualDensityGradientCoefficient405.density_gradient_coefficient_mul_tendsto_L2

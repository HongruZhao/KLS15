import KLSConstantImprovement.ActualDensityGradientCoefficient405

/-! Compact raw-flux test coefficients in the fixed Lebesgue L2 space.
The inverse root has its derived actual-family local bound. The source
density factor is bounded by the actual common potential lower bound. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
namespace KLSConstantImprovement.ActualDensityFluxCoefficient405
open KLS ActualBoundedCanonicalSource ActualSourceFamilyRootPassage405
open ActualDensityWeightedL2405 ActualBoundedCoefficientL2Passage405
open ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricCore
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {ν : ℕ → Measure (Space n)} {μ : Measure (Space n)}

def densityFluxCoefficient (d : SourceData μ) (E : Set (Space n))
    (i a : Fin n) : Space n → ℝ :=
  E.indicator (fun x => canonicalMetricRoot d.potential x i a * densityHalf d.potential x)

theorem density_flux_coefficient_mul_tendsto_L2
    (d : ∀ k, SourceData (ν k)) (d₀ : SourceData μ)
    {κ L P A : ℝ} (hκ : 0 < κ) (hk : ∀ k, κ ≤ (d k).targetConvexityConstant)
    (hV : ∀ k p, L ≤ (d k).targetPotential p)
    (hA : ∀ k x, A ≤ (d k).potential x)
    (hφ : ∀ x, Tendsto (fun k => (d k).potential x) atTop (𝓝 (d₀.potential x)))
    (hH : ∀ᵐ x ∂(volume : Measure (Space n)), Tendsto
      (fun k => coordinateHessian (d k).potential x) atTop (𝓝 (coordinateHessian d₀.potential x)))
    {E : Set (Space n)} (hE : IsCompact E)
    (hp : ∀ k x, x ∈ E → (d k).potential x ≤ P)
    (i a : Fin n) {f : Space n → ℝ} (hf : MemLp f 2 (volume : Measure (Space n))) :
    ∃ (ha : ∀ k, MemLp (fun x => densityFluxCoefficient (d k) E i a x * f x) 2 volume)
      (hb : MemLp (fun x => densityFluxCoefficient d₀ E i a x * f x) 2 volume),
      Tendsto (fun k => (ha k).toLp (fun x => densityFluxCoefficient (d k) E i a x * f x))
        atTop (𝓝 (hb.toLp (fun x => densityFluxCoefficient d₀ E i a x * f x))) := by
  obtain ⟨B, hB, hRb⟩ := actual_family_root_uniform_local_bound d hκ hk hV E hp
  let C : ℝ := B * Real.exp (-A/2)
  have hCn : 0 ≤ C := by dsimp only [C]; positivity
  have hm (k : ℕ) : AEStronglyMeasurable (densityFluxCoefficient (d k) E i a)
      (volume : Measure (Space n)) := by
    have hR : AEStronglyMeasurable (canonicalMetricRoot (d k).potential)
        (volume : Measure (Space n)) :=
      inverseSqrtMatrix_aestronglyMeasurable_of_ae_posDef
        (measurable_coordinateHessian (d k).potential) ((d k).hessian_ae.mono fun _ hx => hx.1)
    have hentry := (continuous_apply a).comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable hR)
    have hρ : Continuous (densityHalf (d k).potential) :=
      Real.continuous_exp.comp ((d k).source_C1.continuous.neg.div_const 2)
    exact (hentry.mul hρ.aestronglyMeasurable).indicator hE.measurableSet
  have hm₀ : AEStronglyMeasurable (densityFluxCoefficient d₀ E i a)
      (volume : Measure (Space n)) := by
    have hR : AEStronglyMeasurable (canonicalMetricRoot d₀.potential)
        (volume : Measure (Space n)) :=
      inverseSqrtMatrix_aestronglyMeasurable_of_ae_posDef
        (measurable_coordinateHessian d₀.potential) (d₀.hessian_ae.mono fun _ hx => hx.1)
    have hentry := (continuous_apply a).comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable hR)
    have hρ : Continuous (densityHalf d₀.potential) :=
      Real.continuous_exp.comp (d₀.source_C1.continuous.neg.div_const 2)
    exact (hentry.mul hρ.aestronglyMeasurable).indicator hE.measurableSet
  have hb (k : ℕ) : ∀ᵐ x ∂(volume : Measure (Space n)),
      ‖densityFluxCoefficient (d k) E i a x‖ ≤ C := by
    filter_upwards [hRb k] with x hx
    by_cases hxE : x ∈ E
    · rw [densityFluxCoefficient, indicator_of_mem hxE, norm_mul]
      have hρ : ‖densityHalf (d k).potential x‖ ≤ Real.exp (-A/2) := by
        rw [densityHalf, Real.norm_of_nonneg (Real.exp_nonneg _)]
        exact Real.exp_le_exp.mpr (by linarith [hA k x])
      exact mul_le_mul (hx hxE i a) hρ (norm_nonneg _) hB.le
    · rw [densityFluxCoefficient, indicator_of_notMem hxE, norm_zero]
      exact hCn
  have ht : ∀ᵐ x ∂(volume : Measure (Space n)), Tendsto
      (fun k => densityFluxCoefficient (d k) E i a x) atTop
      (𝓝 (densityFluxCoefficient d₀ E i a x)) := by
    filter_upwards [actual_family_roots_tendsto_ae d d₀ hH] with x hx
    by_cases hxE : x ∈ E
    · have hR := (((continuous_apply a).comp (continuous_apply i)).continuousAt.tendsto.comp hx.1)
      have hρ := (Real.continuous_exp.tendsto _).comp ((hφ x).neg.div_const 2)
      simpa only [densityFluxCoefficient, indicator_of_mem hxE, densityHalf,
        Function.comp_def] using hR.mul hρ
    · simp only [densityFluxCoefficient, indicator_of_notMem hxE]
      exact tendsto_const_nhds
  have hb₀ : ∀ᵐ x ∂(volume : Measure (Space n)), ‖densityFluxCoefficient d₀ E i a x‖ ≤ C := by
    filter_upwards [ht, ae_all_iff.mpr hb] with x hx hy
    exact le_of_tendsto hx.norm (Eventually.of_forall hy)
  exact bounded_coefficient_mul_tendsto_L2 hm hm₀ hCn hb hb₀ ht hf

end KLSConstantImprovement.ActualDensityFluxCoefficient405
#print axioms KLSConstantImprovement.ActualDensityFluxCoefficient405.density_flux_coefficient_mul_tendsto_L2

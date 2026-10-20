import KLSConstantImprovement.ActualWeakCanonicalMetricCutoffs
import KLSConstantImprovement.ActualBoundedRawMetricDomain

/-! Actual conservative source cutoffs have strongly vanishing metric
gradients in L2. The source constructs the cutoffs and pays their energy;
no cutoff or limiting-error witness is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology ENNReal
namespace KLSConstantImprovement.ActualSourceMetricCutoffGradient405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualWeakCanonicalMetricCore ActualWeakCanonicalMetricCutoffs ActualBoundedRawMetricDomain
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem exists_actual_cutoffs_with_vanishing_metric_gradient (d : SourceData μ) :
    ∃ χ : ℕ → Space n → ℝ,
      (∀ k, ContDiff ℝ 1 (χ k) ∧ HasCompactSupport (χ k) ∧
        ∀ x, χ k x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x, Tendsto (fun k => χ k x) atTop (𝓝 1)) ∧
      (∀ k i, MemLp (canonicalMetricDerivative d.potential (χ k) i) 2
        (potentialMeasure d.potential)) ∧
      ∀ i, Tendsto (fun k => eLpNorm (canonicalMetricDerivative d.potential (χ k) i)
        2 (potentialMeasure d.potential)) atTop (𝓝 0) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  obtain ⟨x₀, _, hc, _, hpoint, _, _, hEi, hElim⟩ := d.exists_metric_energy_cutoffs
  let χ : ℕ → Space n → ℝ := hessianMetricCutoffSequence d.potential x₀
  have hmem (k : ℕ) (i : Fin n) := d.metric_derivative_memLp (hc k).1 (hc k).2.1 i
  refine ⟨χ, hc, hpoint, hmem, ?_⟩
  intro i
  apply tendsto_eLpNorm_zero_of_integral_sq (fun k => hmem k i)
  apply squeeze_zero (fun k => integral_nonneg fun x => sq_nonneg _)
    (fun k => integral_mono_ae (hmem k i).integrable_sq (hEi k) ?_) hElim
  filter_upwards [d.metric_derivative_sq_ae (χ k)] with x hx
  change (canonicalMetricDerivative d.potential (χ k) i x) ^ 2 ≤
    inverseHessianGradientForm d.potential (χ k) x
  rw [← hx]
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin n => (canonicalMetricDerivative d.potential (χ k) j x) ^ 2)
    (fun j _ => sq_nonneg (canonicalMetricDerivative d.potential (χ k) j x))
    (Finset.mem_univ i)

end KLSConstantImprovement.ActualSourceMetricCutoffGradient405
#print axioms KLSConstantImprovement.ActualSourceMetricCutoffGradient405.exists_actual_cutoffs_with_vanishing_metric_gradient

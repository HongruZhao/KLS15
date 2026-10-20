import KLSConstantImprovement.ActualBoundedRawMetricDomain
import KLSConstantImprovement.ActualBoundedSourceCalculus
import KLS.WeakHessianCongruenceEnergy

/-!
Actual canonical form elements for the original source Hessian entries.
The metric gradient uses the stored genuine weak third tensor. Its global
energy is paid by the source's proved trace-energy identity at B=1.
No classical differentiability of a Hessian entry is asserted or used.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceHessianMetricBinding
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualCompactRawMetricGraph ActualBoundedRawMetricDomain
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.hessian_entry_raw_energy_integrable
    {μ : Measure (Space n)} (d : SourceData μ) (a b : Fin n) :
    Integrable (rawInverseHessianGradientForm d.potential (fun k x => d.third x k a b))
      (potentialMeasure d.potential) := by
  have hTs : ∀ᵐ x ∂(volume : Measure (Space n)), ∀ k, Matrix.IsSymm (d.third x k) := by
    filter_upwards [d.third_symmetric_ae] with x hx
    exact fun k => Matrix.IsSymm.ext (fun i j => (hx k j i).2)
  have hA : Integrable (fun x => rawHessianTraceGradientTerm
      (coordinateHessian d.potential x)
      ((1 : Matrix (Fin n) (Fin n) ℝ).transpose * 1) (d.third x))
      (potentialMeasure d.potential) := by
    simpa only [Matrix.transpose_one, Matrix.one_mul] using
      (d.global_trace_energy (B := (1 : Matrix (Fin n) (Fin n) ℝ)) Matrix.PosSemidef.one).2.1
  have he := integrable_raw_hessianCongruence_energy
    (d.hessian_ae.mono fun _ hx => hx.1) d.third_local_L2 hTs
    (1 : Matrix (Fin n) (Fin n) ℝ) hA a b
  simpa only [Matrix.one_mul, Matrix.mul_one, Matrix.transpose_one] using he

theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.hessian_entry_raw_metric_memLp
    {μ : Measure (Space n)} (d : SourceData μ) (a b i : Fin n) :
    MemLp (rawCanonicalMetricDerivative d.potential (fun k x => d.third x k a b) i) 2
      (potentialMeasure d.potential) :=
  d.raw_metric_derivative_memLp_of_energy
    (fun k E hE => d.third_local_L2 k a b E hE)
    (d.hessian_entry_raw_energy_integrable a b) i

/-- The actual Hessian entry and actual weak third-gradient are realized in
the same canonical form graph, with all global energy premises discharged. -/
theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.exists_hessian_entry_metricH1
    {μ : Measure (Space n)} (d : SourceData μ) (a b : Fin n) :
    ∃ U : CanonicalMetricH1 d.potential,
      (canonicalMetricValue d.potential U : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
        (fun x => coordinateHessian d.potential x a b -
          ∫ y, coordinateHessian d.potential y a b ∂potentialMeasure d.potential) ∧
      ∀ i, (canonicalMetricGradient d.potential i U : Space n → ℝ)
        =ᵐ[potentialMeasure d.potential]
          rawCanonicalMetricDerivative d.potential (fun k x => d.third x k a b) i := by
  exact d.bounded_raw_metric_pair_mem
    (measurable_coordinateDerivative (coordinateDerivative d.potential b) a).aestronglyMeasurable
    (fun x => coordinateHessian_entry_bound_of_gradient_lipschitz d.gradient_lipschitz x a b)
    (fun k E hE => d.third_local_L2 k a b E hE)
    (fun k => d.third_weak_derivative k a b) (d.hessian_entry_raw_energy_integrable a b)

theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.hessian_entry_mean_eq_one
    {μ : Measure (Space n)} (d : SourceData μ) (hiso : IsIsotropic μ) (a b : Fin n) :
    (∫ x, coordinateHessian d.potential x a b ∂potentialMeasure d.potential) =
      (1 : Matrix (Fin n) (Fin n) ℝ) a b := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  exact integral_actual_hessian_entry_eq_one_C11 d.source_C1 d.gradient_lipschitz
    (d.pushforward.symm ▸ hiso) a b

theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.exists_centered_hessian_entry_metricH1
    {μ : Measure (Space n)} (d : SourceData μ) (hiso : IsIsotropic μ) (a b : Fin n) :
    ∃ U : CanonicalMetricH1 d.potential,
      (canonicalMetricValue d.potential U : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
        (fun x => coordinateHessian d.potential x a b - (1 : Matrix (Fin n) (Fin n) ℝ) a b) ∧
      ∀ i, (canonicalMetricGradient d.potential i U : Space n → ℝ)
        =ᵐ[potentialMeasure d.potential]
          rawCanonicalMetricDerivative d.potential (fun k x => d.third x k a b) i := by
  obtain ⟨U, hu, hud⟩ := d.exists_hessian_entry_metricH1 a b
  refine ⟨U, ?_, hud⟩
  simpa only [d.hessian_entry_mean_eq_one hiso a b] using hu

end KLSConstantImprovement.ActualSourceHessianMetricBinding
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.hessian_entry_raw_energy_integrable
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.hessian_entry_raw_metric_memLp
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.exists_hessian_entry_metricH1
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.hessian_entry_mean_eq_one
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.exists_centered_hessian_entry_metricH1

import KLSConstantImprovement.ActualSourceLocalDivergence405
import KLSConstantImprovement.ActualLocalDivergenceTests405
import KLSConstantImprovement.ActualBoundedWeakGlobalTest405
import KLSConstantImprovement.ActualSourceRawMetricPair405

/-! Genuine compact raw-H1 testing converts a constructed weighted
local divergence equation to the canonical metric weak equation. The
proof retains local L2 flux and local L1 drift throughout. -/
noncomputable section
open MeasureTheory Matrix Filter Set
open scoped BigOperators ENNReal Topology
namespace KLSConstantImprovement.ActualLocalDivergenceMetricEquation405
open KLS ActualBoundedCanonicalSource ActualSourceLocalDivergence405 ActualLocalDivergenceTests405
open ActualLocalBoundedWeakAlgebra405 ActualLocalCompactWeakTests405 ActualBoundedWeakGlobalForm405
open ActualBoundedWeakCaccioppoli405 ActualSourceRawMetricPair405 ActualSourceLimitFluxDomains405
open ActualCanonicalMetricEnergyGraph ActualCompactRawMetricGraph
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem compact_raw_derivative_pair_integrable (d : SourceData μ) (θ : LocalRawTest n)
    (hc : HasCompactSupport θ.value) (A : Space n → ℝ)
    (hA : ∀ E, IsCompact E → MemLp A 2 (volume.restrict E)) (a : Fin n) :
    Integrable (fun x => A x * θ.derivative a x) (potentialMeasure d.potential) := by
  have hf := memLp_compact_of_localL2 θ.value_local hc
  have hρ := Real.continuous_exp.comp d.source_C1.continuous.neg
  have hAρ (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => Real.exp (-d.potential x) * A x) 2 (volume.restrict E) :=
    memLp_continuous_mul_on_compact hE (hA E hE) hρ
  have hp := ((θ.weak_derivative a).localL2_pairing_mollify hf hc (θ.derivative_local a) hAρ).1
  apply (integrable_potentialMeasure_iff d.source_C1.continuous.measurable).mpr
  exact hp.congr (Eventually.of_forall fun x => by ring)

theorem sourceLocalDivergence_raw_test (d : SourceData μ) (e : SourceLocalDivergence d)
    (θ : LocalRawTest n) (hc : HasCompactSupport θ.value) :
    (∑ a, ∫ x, e.flux a x * θ.derivative a x ∂potentialMeasure d.potential) =
      ∫ x, e.drift x * θ.value x ∂potentialMeasure d.potential := by
  let ρ : Space n → ℝ := fun x => Real.exp (-d.potential x)
  have hρ : Continuous ρ := Real.continuous_exp.comp d.source_C1.continuous.neg
  have hA (a : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => ρ x * e.flux a x) 2 (volume.restrict E) :=
    memLp_continuous_mul_on_compact hE (e.flux_local a E hE) hρ
  obtain ⟨B, hB⟩ := compact_localRawTest_bound θ hc
  have he := (integral_divergence_of_C3_bounded_compact_H1_test hA
    (e.drift_local.continuous_mul hρ) (fun ψ hψ hψc => by
      have ht := e.identity ψ hψ hψc
      simp_rw [integral_potentialMeasure d.source_C1.continuous.measurable] at ht
      simpa only [ρ, mul_assoc, mul_left_comm, mul_comm] using ht)
    θ.value_local hc hB θ.derivative_local θ.weak_derivative).2.2
  simp_rw [integral_potentialMeasure d.source_C1.continuous.measurable]
  simpa only [ρ, mul_assoc, mul_left_comm, mul_comm] using he

theorem compact_raw_metric_pair_integrable (d : SourceData μ) (f θ : LocalRawTest n)
    (hc : HasCompactSupport θ.value) (r : Fin n) :
    Integrable (fun x => rawCanonicalMetricDerivative d.potential f.derivative r x *
      rawCanonicalMetricDerivative d.potential θ.derivative r x) (potentialMeasure d.potential) := by
  have each (a : Fin n) : Integrable (fun x =>
      (canonicalMetricRoot d.potential x r a * rawCanonicalMetricDerivative d.potential f.derivative r x) *
        θ.derivative a x) (potentialMeasure d.potential) := by
    apply compact_raw_derivative_pair_integrable d θ hc _ _ a
    intro E hE
    exact (actualRoot_entry_top_on_compact d hE r a).mul
      (local_raw_metric_derivative_memLp d f r hE)
  apply (integrable_finsetSum Finset.univ fun a _ => each a).congr
  exact Eventually.of_forall fun x => by
    change (∑ a, (canonicalMetricRoot d.potential x r a *
      rawCanonicalMetricDerivative d.potential f.derivative r x) * θ.derivative a x) =
        rawCanonicalMetricDerivative d.potential f.derivative r x *
          ∑ a, canonicalMetricRoot d.potential x r a * θ.derivative a x
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring

theorem rawMetricWeakEquation_of_sourceLocalDivergence (d : SourceData μ)
    (e : SourceLocalDivergence d) (f : LocalRawTest n) (b : Space n → ℝ)
    (hflux : ∀ᵐ x ∂potentialMeasure d.potential,
      (fun a => e.flux a x) = fun a => ∑ r, (coordinateHessian d.potential x)⁻¹ a r * f.derivative r x)
    (hdrift : e.drift =ᵐ[potentialMeasure d.potential] b) : RawMetricWeakEquation d f b := by
  intro θ hc
  have hm (r : Fin n) := compact_raw_metric_pair_integrable d f θ hc r
  have he (a : Fin n) := compact_raw_derivative_pair_integrable d θ hc (e.flux a) (e.flux_local a) a
  calc
    _ = ∫ x, ∑ r, rawCanonicalMetricDerivative d.potential f.derivative r x *
        rawCanonicalMetricDerivative d.potential θ.derivative r x ∂potentialMeasure d.potential :=
      (integral_finsetSum Finset.univ fun r _ => hm r).symm
    _ = ∫ x, ∑ a, e.flux a x * θ.derivative a x ∂potentialMeasure d.potential := by
      apply integral_congr_ae
      filter_upwards [d.hessian_ae_source, hflux, actual_raw_metric_pair_ae d f.derivative θ.derivative] with x hx hf hp
      rw [hp]
      simp only [congrFun hf, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro r _
      rw [hx.1.inv.isHermitian.isSymm.apply r a]
    _ = ∑ a, ∫ x, e.flux a x * θ.derivative a x ∂potentialMeasure d.potential :=
      integral_finsetSum Finset.univ fun a _ => he a
    _ = ∫ x, e.drift x * θ.value x ∂potentialMeasure d.potential :=
      sourceLocalDivergence_raw_test d e θ hc
    _ = _ := integral_congr_ae (hdrift.fun_mul EventuallyEq.rfl)

end KLSConstantImprovement.ActualLocalDivergenceMetricEquation405

#print axioms KLSConstantImprovement.ActualLocalDivergenceMetricEquation405.sourceLocalDivergence_raw_test
#print axioms KLSConstantImprovement.ActualLocalDivergenceMetricEquation405.rawMetricWeakEquation_of_sourceLocalDivergence

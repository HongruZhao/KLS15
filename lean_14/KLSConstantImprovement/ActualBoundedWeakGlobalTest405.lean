import KLSConstantImprovement.ActualBoundedWeakGlobalForm405
import KLSConstantImprovement.ActualSourceMetricCutoffGradient405
import KLSConstantImprovement.ActualWeightedL2PairingContinuity

/-! Exact global testing of a bounded weak solution by a bounded actual
finite-energy raw test. L1 forcing and both cutoff errors are paid using
the actual conservative source cutoffs. -/
noncomputable section
open MeasureTheory Matrix Set Filter
open scoped BigOperators ENNReal Topology
namespace KLSConstantImprovement.ActualBoundedWeakGlobalTest405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph ActualCompactRawMetricGraph
open ActualLocalBoundedWeakAlgebra405 ActualLocalCompactWeakTests405 ActualBoundedWeakGlobalForm405
open ActualBoundedWeakCaccioppoli405 ActualBoundedRawMetricDomain ActualSourceMetricCutoffGradient405
open ActualWeightedL2PairingContinuity
variable {n : ℕ} {μ : Measure (Space n)}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem raw_metric_cutoff_product (d : SourceData μ) (g : LocalRawTest n)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (r : Fin n) (x : Space n) :
    rawCanonicalMetricDerivative d.potential (cutoffLocalRawTest hχ g).derivative r x =
      χ x * rawCanonicalMetricDerivative d.potential g.derivative r x +
        g.value x * canonicalMetricDerivative d.potential χ r x := by
  simp only [rawCanonicalMetricDerivative, cutoffLocalRawTest, LocalRawTest.mul,
    smoothLocalRawTest, canonicalMetricDerivative, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem bounded_weak_global_test (d : SourceData μ) (f g : LocalRawTest n)
    (b : Space n → ℝ) (hb : Integrable b (potentialMeasure d.potential))
    (hf : MemLp f.value ∞ (potentialMeasure d.potential))
    (hg : MemLp g.value ∞ (potentialMeasure d.potential))
    (hweak : RawMetricWeakEquation d f b)
    (hG : ∀ r, MemLp (rawCanonicalMetricDerivative d.potential g.derivative r) 2
      (potentialMeasure d.potential)) :
    (∑ r, ∫ x, rawCanonicalMetricDerivative d.potential f.derivative r x *
      rawCanonicalMetricDerivative d.potential g.derivative r x ∂potentialMeasure d.potential) =
        ∫ x, b x * g.value x ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  obtain ⟨B, hB, hbound⟩ := memLp_top_ae_real_bound hf
  have he := bounded_weak_global_energy d f b hb hB hf hbound hweak
  have hF (r : Fin n) := d.raw_metric_derivative_memLp_of_energy f.derivative_local he r
  let pair : Space n → ℝ := fun x => ∑ r,
    rawCanonicalMetricDerivative d.potential f.derivative r x * rawCanonicalMetricDerivative d.potential g.derivative r x
  let rhs : Space n → ℝ := fun x => b x * g.value x
  have hpair : Integrable pair (potentialMeasure d.potential) :=
    integrable_finsetSum Finset.univ fun r _ => (hF r).integrable_mul (hG r)
  have hrhs : Integrable rhs (potentialMeasure d.potential) := by
    have hm : MemLp (fun x => g.value x * b x) 1 (potentialMeasure d.potential) := hg.mul (memLp_one_iff_integrable.mpr hb)
    exact (hm.integrable le_rfl).congr (Eventually.of_forall fun x => mul_comm _ _)
  obtain ⟨χ, hc, hpoint, hχm, hχlim⟩ := exists_actual_cutoffs_with_vanishing_metric_gradient d
  have hχb (k : ℕ) : ∀ᵐ x ∂potentialMeasure d.potential, ‖χ k x‖ ≤ 1 :=
    Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg ((hc k).2.2 x).1]
      exact ((hc k).2.2 x).2
  have hχmeas (k : ℕ) : AEStronglyMeasurable (χ k) (potentialMeasure d.potential) := (hc k).1.continuous.aestronglyMeasurable
  have hpχ := integral_mul_tendsto_of_ae_bounded_cutoffs hpair hχmeas hχb (Eventually.of_forall hpoint)
  have hrχ := integral_mul_tendsto_of_ae_bounded_cutoffs hrhs hχmeas hχb (Eventually.of_forall hpoint)
  let err : ℕ → ℝ := fun k => ∑ r, ∫ x,
    (g.value x * rawCanonicalMetricDerivative d.potential f.derivative r x) *
      canonicalMetricDerivative d.potential (χ k) r x ∂potentialMeasure d.potential
  have heInt (k : ℕ) (r : Fin n) : Integrable (fun x =>
      (g.value x * rawCanonicalMetricDerivative d.potential f.derivative r x) *
        canonicalMetricDerivative d.potential (χ k) r x) (potentialMeasure d.potential) :=
    (show MemLp (fun x => g.value x * rawCanonicalMetricDerivative d.potential f.derivative r x) 2
      (potentialMeasure d.potential) from hg.mul (hF r)).integrable_mul (hχm k r)
  have herr : Tendsto err atTop (𝓝 0) := by
    have each (r : Fin n) : Tendsto (fun k => ∫ x,
        (g.value x * rawCanonicalMetricDerivative d.potential f.derivative r x) *
          canonicalMetricDerivative d.potential (χ k) r x ∂potentialMeasure d.potential) atTop (𝓝 0) := by
      have hfn : MemLp (fun x => g.value x * rawCanonicalMetricDerivative d.potential f.derivative r x) 2
          (potentialMeasure d.potential) := hg.mul (hF r)
      have ht := tendsto_integral_mul_of_weighted_L2 (fun _ => hfn) (fun k => hχm k r)
        hfn (MemLp.zero : MemLp (0 : Space n → ℝ) 2 (potentialMeasure d.potential))
        (by simp) (by simpa only [sub_zero] using hχlim r)
      simpa only [Pi.zero_apply, mul_zero, integral_zero] using ht
    have ht := tendsto_finsetSum Finset.univ fun r _ => each r
    simpa only [Finset.sum_const_zero] using ht
  have hbalance (k : ℕ) : (∫ x, χ k x * pair x ∂potentialMeasure d.potential) + err k =
      ∫ x, χ k x * rhs x ∂potentialMeasure d.potential := by
    let θ := cutoffLocalRawTest (hc k).1 g
    have ht := hweak θ (hc k).2.1.mul_right
    have hχtop : MemLp (χ k) ∞ (potentialMeasure d.potential) := (hc k).1.continuous.memLp_of_hasCompactSupport (hc k).2.1
    have hfirst (r : Fin n) : Integrable (fun x => χ k x *
        (rawCanonicalMetricDerivative d.potential f.derivative r x *
          rawCanonicalMetricDerivative d.potential g.derivative r x)) (potentialMeasure d.potential) := by
      have hm : MemLp (fun x => χ k x * rawCanonicalMetricDerivative d.potential f.derivative r x) 2
          (potentialMeasure d.potential) := hχtop.mul (hF r)
      exact (hm.integrable_mul (hG r)).congr (Eventually.of_forall fun x => mul_assoc _ _ _)
    have hi (r : Fin n) : (∫ x, rawCanonicalMetricDerivative d.potential f.derivative r x *
        rawCanonicalMetricDerivative d.potential θ.derivative r x ∂potentialMeasure d.potential) =
        (∫ x, χ k x * (rawCanonicalMetricDerivative d.potential f.derivative r x *
          rawCanonicalMetricDerivative d.potential g.derivative r x) ∂potentialMeasure d.potential) +
          ∫ x, (g.value x * rawCanonicalMetricDerivative d.potential f.derivative r x) *
            canonicalMetricDerivative d.potential (χ k) r x ∂potentialMeasure d.potential := by
      calc
        _ = ∫ x, χ k x * (rawCanonicalMetricDerivative d.potential f.derivative r x *
            rawCanonicalMetricDerivative d.potential g.derivative r x) +
              (g.value x * rawCanonicalMetricDerivative d.potential f.derivative r x) *
                canonicalMetricDerivative d.potential (χ k) r x ∂potentialMeasure d.potential := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by
            change rawCanonicalMetricDerivative d.potential f.derivative r x *
              rawCanonicalMetricDerivative d.potential (cutoffLocalRawTest (hc k).1 g).derivative r x = _
            rw [raw_metric_cutoff_product]
            ring
        _ = _ := integral_add (hfirst r) (heInt k r)
    have hs : (∑ r, ∫ x, χ k x * (rawCanonicalMetricDerivative d.potential f.derivative r x *
        rawCanonicalMetricDerivative d.potential g.derivative r x) ∂potentialMeasure d.potential) =
        ∫ x, χ k x * pair x ∂potentialMeasure d.potential := by
      rw [← integral_finsetSum Finset.univ (fun r _ => hfirst r)]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by simp only [pair, Finset.mul_sum]
    simp_rw [hi] at ht
    rw [Finset.sum_add_distrib, hs] at ht
    have hr : (∫ x, b x * θ.value x ∂potentialMeasure d.potential) =
        ∫ x, χ k x * rhs x ∂potentialMeasure d.potential :=
      integral_congr_ae (Eventually.of_forall fun x => by change b x * (χ k x * g.value x) = _; dsimp only [rhs]; ring)
    exact ht.trans hr
  have hleft := hpχ.2.add herr
  have hright : Tendsto (fun k => ∫ x, χ k x * rhs x ∂potentialMeasure d.potential) atTop
      (𝓝 ((∫ x, pair x ∂potentialMeasure d.potential) + 0)) := by simpa only [hbalance] using hleft
  have hout := tendsto_nhds_unique hright hrχ.2
  rw [add_zero] at hout
  change (∫ x, ∑ r, rawCanonicalMetricDerivative d.potential f.derivative r x *
    rawCanonicalMetricDerivative d.potential g.derivative r x ∂potentialMeasure d.potential) = _ at hout
  have hi (r : Fin n) : Integrable (fun x => rawCanonicalMetricDerivative d.potential f.derivative r x *
      rawCanonicalMetricDerivative d.potential g.derivative r x) (potentialMeasure d.potential) :=
    (hF r).integrable_mul (hG r)
  rw [integral_finsetSum Finset.univ (fun r _ => hi r)] at hout
  exact hout

end KLSConstantImprovement.ActualBoundedWeakGlobalTest405
#print axioms KLSConstantImprovement.ActualBoundedWeakGlobalTest405.raw_metric_cutoff_product
#print axioms KLSConstantImprovement.ActualBoundedWeakGlobalTest405.bounded_weak_global_test

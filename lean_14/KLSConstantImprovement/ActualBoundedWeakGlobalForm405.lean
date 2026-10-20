import KLSConstantImprovement.ActualBoundedWeakCaccioppoli405
import KLSConstantImprovement.ActualSourceBoundedMassGammaDomain405
import KLSConstantImprovement.ActualMaximalRawMetricDomain405

/-! A bounded genuine local weak solution with L1 right-hand side is
in the actual global natural form. Conservative metric cutoffs, the
proved local Caccioppoli inequality and positive Fatou pay its energy.
No compact strong-operator core or prior global form membership is used. -/
noncomputable section
open MeasureTheory Matrix Set Filter
open scoped BigOperators ENNReal Topology
namespace KLSConstantImprovement.ActualBoundedWeakGlobalForm405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph ActualCompactRawMetricGraph
open ActualLocalBoundedWeakAlgebra405 ActualBoundedWeakCaccioppoli405 ActualBoundedRawMetricDomain
open ActualUniformIntegralFatou405 ActualSourceBoundedMassGammaDomain405 ActualMaximalRawMetricDomain405
variable {n : ℕ} {μ : Measure (Space n)}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def RawMetricWeakEquation (d : SourceData μ) (f : LocalRawTest n) (b : Space n → ℝ) : Prop :=
  ∀ θ : LocalRawTest n, HasCompactSupport θ.value →
    (∑ r, ∫ x, rawCanonicalMetricDerivative d.potential f.derivative r x *
      rawCanonicalMetricDerivative d.potential θ.derivative r x ∂potentialMeasure d.potential) =
        ∫ x, b x * θ.value x ∂potentialMeasure d.potential

theorem memLp_top_ae_real_bound {ν : Measure (Space n)} {f : Space n → ℝ} (hf : MemLp f ∞ ν) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ x ∂ν, ‖f x‖ ≤ B := by
  have he := hf.eLpNorm_lt_top
  rw [eLpNorm_exponent_top hf.aestronglyMeasurable] at he
  obtain ⟨B, hB⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp he
  have hBn : ∀ᵐ x ∂ν, ‖f x‖₊ ≤ B := Filter.eventually_map.mp hB
  refine ⟨(B : ℝ), by positivity, hBn.mono fun x hx => ?_⟩
  exact_mod_cast hx

theorem bounded_weak_global_energy (d : SourceData μ) (f : LocalRawTest n)
    (b : Space n → ℝ) (hb : Integrable b (potentialMeasure d.potential))
    {B : ℝ} (hB : 0 ≤ B) (hf : MemLp f.value ∞ (potentialMeasure d.potential))
    (hbound : ∀ᵐ x ∂potentialMeasure d.potential, ‖f.value x‖ ≤ B)
    (hweak : RawMetricWeakEquation d f b) :
    Integrable (rawInverseHessianGradientForm d.potential f.derivative) (potentialMeasure d.potential) := by
  obtain ⟨x₀, _, hc, _, hlim, _, _, hEi, hElim⟩ := d.exists_metric_energy_cutoffs
  let χ : ℕ → Space n → ℝ := hessianMetricCutoffSequence d.potential x₀
  let G : Space n → ℝ := fun x => ∑ r, rawCanonicalMetricDerivative d.potential f.derivative r x ^ 2
  let F : ℕ → Space n → ℝ := fun k x => ∑ r, (χ k x * rawCanonicalMetricDerivative d.potential f.derivative r x) ^ 2
  have hFi (k : ℕ) : Integrable (F k) (potentialMeasure d.potential) :=
    integrable_finsetSum Finset.univ fun r _ => (cutoff_raw_metric_derivative_memLp d f (hc k).1 (hc k).2.1 r).integrable_sq
  have hFlim (x : Space n) : Tendsto (fun k => F k x) atTop (𝓝 (G x)) := by
    apply tendsto_finset_sum
    intro r _
    simpa only [one_mul] using ((hlim x).mul_const (rawCanonicalMetricDerivative d.potential f.derivative r x)).pow 2
  have hGm : AEStronglyMeasurable G (potentialMeasure d.potential) :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hFi k).aestronglyMeasurable) (Eventually.of_forall hFlim)
  have hcut (k : ℕ) : (∑ r, ∫ x, canonicalMetricDerivative d.potential (χ k) r x ^ 2 ∂potentialMeasure d.potential) =
      ∫ x, inverseHessianGradientForm d.potential (χ k) x ∂potentialMeasure d.potential := by
    rw [← integral_finsetSum Finset.univ (fun r _ => (d.metric_derivative_memLp (hc k).1 (hc k).2.1 r).integrable_sq)]
    exact integral_congr_ae (d.metric_derivative_sq_ae (χ k))
  have hlocal (k : ℕ) : (∫ x, F k x ∂potentialMeasure d.potential) ≤
      2 * B * (∫ x, |b x| ∂potentialMeasure d.potential) +
        4 * B ^ 2 * (∫ x, inverseHessianGradientForm d.potential (χ k) x ∂potentialMeasure d.potential) := by
    have he := bounded_weak_caccioppoli d f b hb hB hf hbound hweak (hc k).1 (hc k).2.1 (hc k).2.2
    rw [hcut] at he
    rw [integral_finsetSum Finset.univ (fun r _ =>
      (cutoff_raw_metric_derivative_memLp d f (hc k).1 (hc k).2.1 r).integrable_sq)]
    exact he
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hElim.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  let C : ℝ := 2 * B * (∫ x, |b x| ∂potentialMeasure d.potential) + 4 * B ^ 2
  have hC : 0 ≤ C := by
    have hi : 0 ≤ ∫ x, |b x| ∂potentialMeasure d.potential := integral_nonneg (fun x => abs_nonneg (b x))
    dsimp only [C]
    positivity
  have hboundF (k : ℕ) : (∫ x, ‖F (k + N) x‖ ∂potentialMeasure d.potential) ≤ C := by
    have he : (∫ x, ‖F (k + N) x‖ ∂potentialMeasure d.potential) = ∫ x, F (k + N) x ∂potentialMeasure d.potential := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => Real.norm_of_nonneg (Finset.sum_nonneg fun r _ => sq_nonneg _)
    rw [he]
    have hn := (hN (k + N) (Nat.le_add_left N k)).le
    have hp := mul_le_mul_of_nonneg_left hn (show 0 ≤ 4 * B ^ 2 by positivity)
    have hl := hlocal (k + N)
    dsimp only [C]
    nlinarith only [hl, hp]
  obtain ⟨hGi, _⟩ := integrable_and_integral_norm_le_of_tendsto_uniform_bound hGm
    (fun k => hFi (k + N)) (Eventually.of_forall fun x => (hFlim x).comp (tendsto_add_atTop_nat N)) hC hboundF
  exact hGi.congr (d.raw_metric_derivative_sq_ae f.derivative)

theorem exists_bounded_weak_global_form (d : SourceData μ) (f : LocalRawTest n)
    (b : Space n → ℝ) (hb : Integrable b (potentialMeasure d.potential))
    (hf : MemLp f.value ∞ (potentialMeasure d.potential)) (hweak : RawMetricWeakEquation d f b) :
    ∃ U : CanonicalMetricH1 d.potential,
      (canonicalMetricValue d.potential U : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
        (fun x => f.value x - ∫ y, f.value y ∂potentialMeasure d.potential) ∧
      ∀ r, (canonicalMetricGradient d.potential r U : Space n → ℝ)
        =ᵐ[potentialMeasure d.potential] rawCanonicalMetricDerivative d.potential f.derivative r := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  obtain ⟨B, hB, hbound⟩ := memLp_top_ae_real_bound hf
  have he := bounded_weak_global_energy d f b hb hB hf hbound hweak
  exact d.maximal_raw_metric_pair_mem (hf.mono_exponent (by simp)) f.derivative_local f.weak_derivative he

end KLSConstantImprovement.ActualBoundedWeakGlobalForm405
#print axioms KLSConstantImprovement.ActualBoundedWeakGlobalForm405.bounded_weak_global_energy
#print axioms KLSConstantImprovement.ActualBoundedWeakGlobalForm405.exists_bounded_weak_global_form

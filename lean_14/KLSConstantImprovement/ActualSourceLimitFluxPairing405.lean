import KLSConstantImprovement.ActualSourceLimitFluxDomains405
import KLSConstantImprovement.ActualFiniteFamilyWeakPassage405

/-! The original-source flux block has actual compact pairings, and
those pairings pass to the constructed global energy weak limit. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceLimitFluxPairing405
open KLS ActualBoundedCanonicalSource ActualSourceRegularizedEnergyVector405
open ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricSmoothing
open ActualSourceLimitFluxDomains405 ActualFiniteFamilyWeakPassage405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem integral_lp_mul_eq_inner_toLp {ν : Measure (Space n)}
    (f : Lp ℝ 2 ν) {b : Space n → ℝ} (hb : MemLp b 2 ν) :
    (∫ x, f x * b x ∂ν) = inner ℝ f (hb.toLp b) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hb.coeFn_toLp] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial]
  ring

theorem actual_root_mul_compact_memLp (d : SourceData μ)
    {ψ : Space n → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (i a : Fin n) :
    MemLp (fun x => canonicalMetricRoot d.potential x i a * ψ x) 2 (potentialMeasure d.potential) := by
  have hψ2 := memLp_of_continuous_hasCompactSupport d.source_C1.continuous hψ hc
  have hm : MemLp (fun x => (tsupport ψ).indicator (fun y => canonicalMetricRoot d.potential y i a) x * ψ x)
      2 (potentialMeasure d.potential) := (d.compact_metricRoot_entry_top hc i a).mul hψ2
  apply (memLp_congr_ae (Eventually.of_forall fun x => ?_)).mp hm
  by_cases hx : x ∈ tsupport ψ
  · rw [indicator_of_mem hx]
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]

theorem flux_compact_pair_eq_inner_sum (d : SourceData μ) (V : GaffneyEnergyAmbient d)
    {ψ : Space n → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (i : Fin n) :
    (∫ x, energyLimitFlux d V i x * ψ x ∂potentialMeasure d.potential) =
      ∑ a : Fin n, inner ℝ (V (Sum.inl a))
        ((actual_root_mul_compact_memLp d hψ hc i a).toLp
          (fun x => canonicalMetricRoot d.potential x i a * ψ x)) := by
  have hi (a : Fin n) : Integrable (fun x => V (Sum.inl a) x *
      (canonicalMetricRoot d.potential x i a * ψ x)) (potentialMeasure d.potential) :=
    (Lp.memLp _).integrable_mul (actual_root_mul_compact_memLp d hψ hc i a)
  calc
    _ = ∫ x, ∑ a : Fin n, V (Sum.inl a) x * (canonicalMetricRoot d.potential x i a * ψ x)
        ∂potentialMeasure d.potential := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [energyLimitFlux, Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by ring
    _ = ∑ a : Fin n, ∫ x, V (Sum.inl a) x * (canonicalMetricRoot d.potential x i a * ψ x)
        ∂potentialMeasure d.potential := integral_finsetSum Finset.univ (fun a _ => hi a)
    _ = _ := Finset.sum_congr rfl fun a _ => integral_lp_mul_eq_inner_toLp _ _

theorem energyLimitFlux_compact_pair_tendsto (d : SourceData μ)
    {W : ℕ → GaffneyEnergyAmbient d} {V : GaffneyEnergyAmbient d}
    (hw : ∀ Y, Tendsto (fun k => inner ℝ (W k) Y) atTop (𝓝 (inner ℝ V Y)))
    {ψ : Space n → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (i : Fin n) :
    Tendsto (fun k => ∫ x, energyLimitFlux d (W k) i x * ψ x ∂potentialMeasure d.potential) atTop
      (𝓝 (∫ x, energyLimitFlux d V i x * ψ x ∂potentialMeasure d.potential)) := by
  have ht := tendsto_finsetSum Finset.univ (fun a _ =>
    finite_family_weak_coordinate_tendsto hw (Sum.inl a)
      ((actual_root_mul_compact_memLp d hψ hc i a).toLp
        (fun x => canonicalMetricRoot d.potential x i a * ψ x)))
  rw [flux_compact_pair_eq_inner_sum d V hψ hc i]
  exact ht.congr fun k => (flux_compact_pair_eq_inner_sum d (W k) hψ hc i).symm

end KLSConstantImprovement.ActualSourceLimitFluxPairing405
#print axioms KLSConstantImprovement.ActualSourceLimitFluxPairing405.integral_lp_mul_eq_inner_toLp
#print axioms KLSConstantImprovement.ActualSourceLimitFluxPairing405.actual_root_mul_compact_memLp
#print axioms KLSConstantImprovement.ActualSourceLimitFluxPairing405.flux_compact_pair_eq_inner_sum
#print axioms KLSConstantImprovement.ActualSourceLimitFluxPairing405.energyLimitFlux_compact_pair_tendsto

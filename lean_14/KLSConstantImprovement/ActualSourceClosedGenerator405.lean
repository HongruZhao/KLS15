import KLSConstantImprovement.ActualSourceConservativeResolvent405
import KLSConstantImprovement.ActualSourceMetricFaithfulness405
import KLS.WeightedResolventWeakEquation
import KLS.ProbabilityMeanCentering
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
A concrete closed scalar generator graph for the actual inverse-Hessian
source form. Compact-test separation proves injectivity of the constructed
conservative resolvent; the resulting graph is single-valued, closed,
symmetric and positive. These are conclusions on the actual source, not
an assumed closed operator package. Literal compact diffusion action is
bound separately.
-/

noncomputable section
open MeasureTheory InnerProductSpace Set Filter
open scoped BigOperators ContDiff RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceClosedGenerator405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualCanonicalMetricResolvent ActualWeakCanonicalMetricInverse
open ActualSourceConservativeResolvent405 ActualSourceMetricFaithfulness405
variable {n : ℕ} {μ : Measure (Space n)}

/-- The actual compact form values separate actual centered source L2 data. -/
theorem datum_eq_zero_of_annihilates_form_values (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0)
    (hpair : ∀ V : CanonicalMetricH1 d.potential,
      inner ℝ g (canonicalMetricValue d.potential V) = 0) : g = 0 := by
  letI := d.source_probability
  have hae : ∀ᵐ x ∂potentialMeasure d.potential, g x = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((Lp.memLp g).integrable (by norm_num)).locallyIntegrable
    intro ψ hψ hc
    obtain ⟨V, hv, _⟩ := exists_sourceMetricH1_of_smoothCompact d (hψ.of_le (by simp)) hc
    have hψ2 := memLp_of_continuous_hasCompactSupport d.source_C1.continuous hψ.continuous hc
    have ht := hpair V
    rw [weighted_inner_centered_test hψ2 hv, hg, zero_mul, sub_zero] at ht
    simpa only [smul_eq_mul, mul_comm] using ht
  apply Lp.ext
  filter_upwards [hae, Lp.coeFn_zero ℝ 2 (potentialMeasure d.potential)] with x hx hz
  exact hx.trans hz.symm

/-- Restoring the mean removes the constant kernel of the centered form. -/
theorem sourceConservativeResolvent_eq_zero_iff (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    sourceConservativeResolvent d (t := 1) zero_lt_one g = 0 ↔ g = 0 := by
  letI := d.source_probability
  constructor
  · intro hR
    have hg : (∫ x, g x ∂potentialMeasure d.potential) = 0 := by
      rw [← sourceConservativeResolvent_integral d zero_lt_one g, hR]
      exact integral_eq_zero_of_ae (Lp.coeFn_zero ℝ 2 (potentialMeasure d.potential))
    have hcr : canonicalResolvent d.potential (t := 1) zero_lt_one g = 0 := by
      have hc := center_sourceConservativeResolvent d (t := 1) zero_lt_one g
      rw [hR, centeredResolvent_center d zero_lt_one g] at hc
      have hz : CenteredL2.center (potentialMeasure d.potential)
          (0 : Lp ℝ 2 (potentialMeasure d.potential)) = 0 := by
        rw [← CenteredL2.centerCLM_apply, map_zero]
      exact hc.symm.trans hz
    have hU : canonicalResolventH1 d.potential (t := 1) zero_lt_one g = 0 := by
      apply metricH1_eq_zero_of_value_eq_zero d
      exact hcr
    apply datum_eq_zero_of_annihilates_form_values d g hg
    intro V
    have he := canonicalResolvent_variational d.potential (t := 1) zero_lt_one g V
    simp only [canonicalResolvent, ContinuousLinearMap.comp_apply, hU, map_zero,
      inner_zero_left, zero_apply, mul_zero, zero_add] at he
    exact he.symm
  · rintro rfl
    exact map_zero _

theorem sourceConservativeResolvent_injective (d : SourceData μ) :
    Function.Injective (sourceConservativeResolvent d (t := 1) zero_lt_one) := by
  intro f g hfg
  apply sub_eq_zero.mp
  apply (sourceConservativeResolvent_eq_zero_iff d (f - g)).mp
  rw [map_sub, hfg, sub_self]

/-- Its actual generator energy is precisely the actual canonical form
energy of its centered variational representative. -/
theorem generator_resolvent_energy_identity (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    inner ℝ (g - sourceConservativeResolvent d (t := 1) zero_lt_one g)
      (sourceConservativeResolvent d (t := 1) zero_lt_one g) =
      canonicalMetricEnergy d.potential (canonicalResolventH1 d.potential (t := 1) zero_lt_one g)
        (canonicalResolventH1 d.potential (t := 1) zero_lt_one g) := by
  letI := d.source_probability
  let m := weightedMassProjection d.potential g
  let u := canonicalResolvent d.potential (t := 1) zero_lt_one g
  have ho : inner ℝ m u = 0 := by
    rw [show m = weightedMassProjection d.potential g from rfl,
      weightedMassProjection_apply, inner_smul_left, CenteredL2.inner_oneLp,
      centeredResolvent_integral_eq_zero d zero_lt_one g, mul_zero]
  have hm : inner ℝ g m = ‖m‖ ^ 2 := by
    dsimp [m]
    rw [weightedMassProjection_apply, inner_smul_right,
      real_inner_comm (CenteredL2.oneLp (potentialMeasure d.potential)) g,
      CenteredL2.inner_oneLp, norm_smul, mul_pow, CenteredL2.oneLp_norm_sq,
      Real.norm_eq_abs, sq_abs]
    ring
  have he := canonicalResolvent_energy_identity d.potential (t := 1) zero_lt_one g
  have hn := norm_add_sq_real m u
  have hr : sourceConservativeResolvent d (t := 1) zero_lt_one g = m + u := rfl
  rw [ho, mul_zero, add_zero, ← hr] at hn
  have hg : inner ℝ g (sourceConservativeResolvent d (t := 1) zero_lt_one g) =
      ‖m‖ ^ 2 + inner ℝ g u := by rw [hr, inner_add_right, hm]
  rw [inner_sub_left, real_inner_self_eq_norm_sq, hg]
  change ‖u‖ ^ 2 + 1 * _ = inner ℝ g u at he
  nlinarith

def sourceGeneratorConstraint (d : SourceData μ) :
    (Lp ℝ 2 (potentialMeasure d.potential) × Lp ℝ 2 (potentialMeasure d.potential)) →L[ℝ]
      Lp ℝ 2 (potentialMeasure d.potential) :=
  ContinuousLinearMap.fst ℝ _ _ -
    (sourceConservativeResolvent d (t := 1) zero_lt_one).comp
      (ContinuousLinearMap.fst ℝ _ _ + ContinuousLinearMap.snd ℝ _ _)

/-- The graph f=R1(f+Af), using the actually constructed conservative R1. -/
def sourceGeneratorGraph (d : SourceData μ) :
    Submodule ℝ (Lp ℝ 2 (potentialMeasure d.potential) × Lp ℝ 2 (potentialMeasure d.potential)) :=
  LinearMap.ker (sourceGeneratorConstraint d).toLinearMap

theorem mem_sourceGeneratorGraph_iff (d : SourceData μ)
    (f af : Lp ℝ 2 (potentialMeasure d.potential)) :
    (f, af) ∈ sourceGeneratorGraph d ↔
      f = sourceConservativeResolvent d (t := 1) zero_lt_one (f + af) := by
  change f - sourceConservativeResolvent d (t := 1) zero_lt_one (f + af) = 0 ↔ _
  exact sub_eq_zero

theorem sourceGeneratorGraph_closed (d : SourceData μ) :
    IsClosed (sourceGeneratorGraph d : Set
      (Lp ℝ 2 (potentialMeasure d.potential) × Lp ℝ 2 (potentialMeasure d.potential))) :=
  (sourceGeneratorConstraint d).isClosed_ker

theorem sourceGeneratorGraph_singleValued (d : SourceData μ)
    {f a b : Lp ℝ 2 (potentialMeasure d.potential)}
    (ha : (f, a) ∈ sourceGeneratorGraph d) (hb : (f, b) ∈ sourceGeneratorGraph d) : a = b := by
  rw [mem_sourceGeneratorGraph_iff] at ha hb
  have he := sourceConservativeResolvent_injective d (ha.symm.trans hb)
  exact add_left_cancel he

theorem sourceGeneratorGraph_symmetric (d : SourceData μ)
    {f af g ag : Lp ℝ 2 (potentialMeasure d.potential)}
    (hf : (f, af) ∈ sourceGeneratorGraph d) (hg : (g, ag) ∈ sourceGeneratorGraph d) :
    inner ℝ af g = inner ℝ f ag := by
  have hrf := (mem_sourceGeneratorGraph_iff d f af).mp hf
  have hrg := (mem_sourceGeneratorGraph_iff d g ag).mp hg
  have hs := sourceConservativeResolvent_symmetric d (t := 1) zero_lt_one (f + af) (g + ag)
  rw [← hrf, ← hrg, inner_add_right, inner_add_left] at hs
  linarith

theorem sourceGeneratorGraph_nonnegative (d : SourceData μ)
    {f af : Lp ℝ 2 (potentialMeasure d.potential)}
    (hf : (f, af) ∈ sourceGeneratorGraph d) : 0 ≤ inner ℝ af f := by
  have hr := (mem_sourceGeneratorGraph_iff d f af).mp hf
  have he := generator_resolvent_energy_identity d (f + af)
  rw [← hr, add_sub_cancel_left] at he
  rw [he, canonicalMetricEnergy_self]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

end KLSConstantImprovement.ActualSourceClosedGenerator405

#print axioms KLSConstantImprovement.ActualSourceClosedGenerator405.sourceConservativeResolvent_injective
#print axioms KLSConstantImprovement.ActualSourceClosedGenerator405.generator_resolvent_energy_identity
#print axioms KLSConstantImprovement.ActualSourceClosedGenerator405.sourceGeneratorGraph_closed
#print axioms KLSConstantImprovement.ActualSourceClosedGenerator405.sourceGeneratorGraph_singleValued
#print axioms KLSConstantImprovement.ActualSourceClosedGenerator405.sourceGeneratorGraph_symmetric
#print axioms KLSConstantImprovement.ActualSourceClosedGenerator405.sourceGeneratorGraph_nonnegative

import KLSConstantImprovement.ActualSourceL1Comparison405
import KLS.WeightedResolventWeakEquation
import KLS.ProbabilityMeanCentering

/-!
The actual conservative unit resolvent dominates half an observable
whose actual weak form evolution is H-S with S positive in L1. Every
compact equation and mean correction used by the L1 maximum principle
is derived below. S is never declared to lie in L2 or in a generator
domain. The source Hessian supplies the observable in the next leaf.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter InnerProductSpace
open scoped BigOperators ContDiff Topology RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceL1ResolventLower405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualCanonicalMetricResolvent ActualWeakCanonicalMetricInverse
open ActualSourceConservativeResolvent405 ActualSourceResolventOrder405 ActualSourceL1Comparison405
variable {n : ℕ} {μ : Measure (Space n)}

theorem sourceR1_form_compact_equation (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ)
    (V : CanonicalMetricH1 d.potential)
    (hv : (canonicalMetricValue d.potential V : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      fun x => ψ x - ∫ y, ψ y ∂potentialMeasure d.potential) :
    canonicalMetricEnergy d.potential (canonicalResolventH1 d.potential (t := 1) zero_lt_one g) V =
      ∫ x, (g x - sourceConservativeResolvent d (t := 1) zero_lt_one g x) * ψ x
        ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hψ2 := memLp_of_continuous_hasCompactSupport d.source_C1.continuous hψ.continuous hc
  have hfull : inner ℝ (sourceConservativeResolvent d (t := 1) zero_lt_one g)
      (canonicalMetricValue d.potential V) =
      inner ℝ (canonicalResolvent d.potential (t := 1) zero_lt_one g)
        (canonicalMetricValue d.potential V) := by
    rw [sourceConservativeResolvent_apply, inner_add_left, weightedMassProjection_apply,
      inner_smul_left, CenteredL2.inner_oneLp,
      canonicalMetricValue_integral_eq_zero d.source_C1.continuous V, mul_zero, zero_add]
  have he := canonicalResolvent_variational d.potential (t := 1) zero_lt_one g V
  rw [← hfull, weighted_inner_centered_test hψ2 hv, weighted_inner_centered_test hψ2 hv,
    sourceConservativeResolvent_integral d zero_lt_one g, one_mul] at he
  have hgψ : Integrable (fun x => g x * ψ x) (potentialMeasure d.potential) :=
    (Lp.memLp g).integrable_mul hψ2
  have hRψ : Integrable (fun x => sourceConservativeResolvent d (t := 1) zero_lt_one g x * ψ x)
      (potentialMeasure d.potential) := (Lp.memLp _).integrable_mul hψ2
  have hsplit : (∫ x, (g x - sourceConservativeResolvent d (t := 1) zero_lt_one g x) * ψ x
      ∂potentialMeasure d.potential) =
      (∫ x, g x * ψ x ∂potentialMeasure d.potential) -
        ∫ x, sourceConservativeResolvent d (t := 1) zero_lt_one g x * ψ x
          ∂potentialMeasure d.potential := by
    rw [← integral_sub hgψ hRψ]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  rw [hsplit]
  linarith

private theorem energy_smul_left (φ : Space n → ℝ) (a : ℝ)
    (U V : CanonicalMetricH1 φ) :
    canonicalMetricEnergy φ (a • U) V = a * canonicalMetricEnergy φ U V := by
  have hm : canonicalMetricEnergy φ (a • U) = a • canonicalMetricEnergy φ U :=
    (canonicalMetricEnergy φ).map_smul a U
  have he := congrArg (fun L : CanonicalMetricH1 φ →L[ℝ] ℝ => L V) hm
  simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using he

/-- Natural variational L1 comparison, with the forcing sign and every
compact equation paid before the form-limit passage. -/
theorem fullR1_twice_ge_of_actual_L1_form_evolution (d : SourceData μ)
    (h : Lp ℝ 2 (potentialMeasure d.potential)) (Z : CanonicalMetricH1 d.potential)
    (S : Space n → ℝ) (hS : Integrable S (potentialMeasure d.potential))
    (hSpos : ∀ᵐ x ∂potentialMeasure d.potential, 0 ≤ S x)
    (hmean : (∫ x, S x ∂potentialMeasure d.potential) =
      ∫ x, h x ∂potentialMeasure d.potential)
    (hZ : canonicalMetricValue d.potential Z =
      letI := d.source_probability; CenteredL2.center (potentialMeasure d.potential) h)
    (hZequation : ∀ (ψ : Space n → ℝ), ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      ∀ V : CanonicalMetricH1 d.potential,
        (canonicalMetricValue d.potential V : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
          (fun x => ψ x - ∫ y, ψ y ∂potentialMeasure d.potential) →
        (∀ i : Fin n, (canonicalMetricGradient d.potential i V : Space n → ℝ)
          =ᵐ[potentialMeasure d.potential] canonicalMetricDerivative d.potential ψ i) →
        canonicalMetricEnergy d.potential Z V =
          ∫ x, (h x - S x) * ψ x ∂potentialMeasure d.potential) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      h x ≤ 2 * sourceConservativeResolvent d (t := 1) zero_lt_one h x := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let K := sourceConservativeResolvent d (t := 1) zero_lt_one h
  let Y := canonicalResolventH1 d.potential (t := 1) zero_lt_one h
  let r : Lp ℝ 2 (potentialMeasure d.potential) := h - (2 : ℝ) • K
  let U : CanonicalMetricH1 d.potential := Z - (2 : ℝ) • Y
  have hr_ae : (r : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      fun x => h x - 2 * K x := by
    filter_upwards [Lp.coeFn_sub h ((2 : ℝ) • K), Lp.coeFn_smul (2 : ℝ) K] with x hx hy
    change (h - (2 : ℝ) • K) x = _
    rw [hx, Pi.sub_apply, hy, Pi.smul_apply, smul_eq_mul]
  have hrmean : (∫ x, r x ∂potentialMeasure d.potential) =
      -(∫ x, h x ∂potentialMeasure d.potential) := by
    calc
      _ = inner ℝ (CenteredL2.oneLp (potentialMeasure d.potential)) r :=
        (CenteredL2.inner_oneLp _ _).symm
      _ = _ := by
        change inner ℝ (CenteredL2.oneLp (potentialMeasure d.potential))
          (h - (2 : ℝ) • sourceConservativeResolvent d (t := 1) zero_lt_one h) = _
        rw [inner_sub_right, inner_smul_right, CenteredL2.inner_oneLp,
          CenteredL2.inner_oneLp, sourceConservativeResolvent_integral d zero_lt_one h]
        ring
  have hUvalue : canonicalMetricValue d.potential U = CenteredL2.center (potentialMeasure d.potential) r := by
    have hcenterK : CenteredL2.center (potentialMeasure d.potential) K =
        canonicalMetricValue d.potential Y := by
      dsimp only [K]
      rw [center_sourceConservativeResolvent, centeredResolvent_center d zero_lt_one h]
      rfl
    change canonicalMetricValue d.potential (Z - (2 : ℝ) • Y) =
      CenteredL2.center (potentialMeasure d.potential) (h - (2 : ℝ) • K)
    rw [map_sub, map_smul, hZ]
    conv_rhs => rw [← CenteredL2.centerCLM_apply]
    rw [map_sub, map_smul, CenteredL2.centerCLM_apply, CenteredL2.centerCLM_apply, hcenterK]
  have hrep : r = (∫ x, r x ∂potentialMeasure d.potential) •
      CenteredL2.oneLp (potentialMeasure d.potential) + canonicalMetricValue d.potential U := by
    rw [hUvalue, CenteredL2.center]
    abel
  have hmeanr : (∫ x, -S x ∂potentialMeasure d.potential) =
      ∫ x, r x ∂potentialMeasure d.potential := by rw [integral_neg, hmean, hrmean]
  have hweak : ∀ (ψ : Space n → ℝ), ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      ∀ V : CanonicalMetricH1 d.potential,
        (canonicalMetricValue d.potential V : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
          (fun x => ψ x - ∫ y, ψ y ∂potentialMeasure d.potential) →
        (∀ i : Fin n, (canonicalMetricGradient d.potential i V : Space n → ℝ)
          =ᵐ[potentialMeasure d.potential] canonicalMetricDerivative d.potential ψ i) →
        canonicalMetricEnergy d.potential U V =
          ∫ x, (-S x - r x) * ψ x ∂potentialMeasure d.potential := by
    intro ψ hψ hc V hv hd
    have hψ2 := memLp_of_continuous_hasCompactSupport d.source_C1.continuous hψ.continuous hc
    obtain ⟨C, hC⟩ := hψ.continuous.bounded_above_of_compact_support hc
    have hSψ : Integrable (fun x => S x * ψ x) (potentialMeasure d.potential) :=
      hS.mul_bdd hψ.continuous.aestronglyMeasurable (Eventually.of_forall hC)
    have hhψ : Integrable (fun x => h x * ψ x) (potentialMeasure d.potential) :=
      (Lp.memLp h).integrable_mul hψ2
    have hKψ : Integrable (fun x => K x * ψ x) (potentialMeasure d.potential) :=
      (Lp.memLp K).integrable_mul hψ2
    have hZψ : Integrable (fun x => (h x - S x) * ψ x) (potentialMeasure d.potential) :=
      (hhψ.sub hSψ).congr (Eventually.of_forall fun x => by
        change h x * ψ x - S x * ψ x = (h x - S x) * ψ x
        ring)
    have hYψ : Integrable (fun x => (h x - K x) * ψ x) (potentialMeasure d.potential) :=
      (hhψ.sub hKψ).congr (Eventually.of_forall fun x => by
        change h x * ψ x - K x * ψ x = (h x - K x) * ψ x
        ring)
    change canonicalMetricEnergy d.potential (Z - (2 : ℝ) • Y) V = _
    rw [canonicalMetricEnergy_sub_left, energy_smul_left,
      hZequation ψ hψ hc V hv hd, sourceR1_form_compact_equation d h hψ hc V hv]
    rw [← integral_const_mul, ← integral_sub hZψ (hYψ.const_mul 2)]
    apply integral_congr_ae
    filter_upwards [hr_ae] with x hx
    rw [hx]
    change (h x - S x) * ψ x - 2 * ((h x - K x) * ψ x) = _
    ring
  have hnonpos := ae_nonpos_of_actual_L1_compact_equation d U r (fun x => -S x)
    hS.neg (hSpos.mono fun _ hx => neg_nonpos.mpr hx) hmeanr hrep hweak
  filter_upwards [hnonpos, hr_ae] with x hx hrx
  rw [hrx] at hx
  exact sub_nonpos.mp hx

end KLSConstantImprovement.ActualSourceL1ResolventLower405

#print axioms KLSConstantImprovement.ActualSourceL1ResolventLower405.sourceR1_form_compact_equation
#print axioms KLSConstantImprovement.ActualSourceL1ResolventLower405.fullR1_twice_ge_of_actual_L1_form_evolution

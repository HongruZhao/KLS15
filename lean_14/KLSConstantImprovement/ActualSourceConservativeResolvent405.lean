import KLSConstantImprovement.ActualWeakCanonicalMetricInverse
import KLS.WeightedMassResolvent

/-!
The inverse-Hessian form graph is centered. Its variational resolvent
annihilates constants. This file restores the actual mean, constructing
the conservative full L2 resolvent on the same actual canonical source.
The sharp centered 1/(1+t) bound follows from the proved source BL form.
Positivity preservation and L1 production pairing are separate obligations.
-/

noncomputable section
open MeasureTheory InnerProductSpace
open scoped BigOperators ContDiff RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceConservativeResolvent405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualCanonicalMetricResolvent ActualWeakCanonicalMetricInverse
variable {n : ℕ} {μ : Measure (Space n)}

theorem centeredResolvent_unique (φ : Space n → ℝ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) {U : CanonicalMetricH1 φ}
    (hU : ∀ V, inner ℝ (canonicalMetricValue φ U) (canonicalMetricValue φ V) +
      t * canonicalMetricEnergy φ U V = inner ℝ g (canonicalMetricValue φ V)) :
    U = canonicalResolventH1 φ ht g := by
  let hc := canonicalShiftedEnergy_isCoercive φ ht
  have he : (canonicalMetricValue φ).adjoint g = hc.continuousLinearEquivOfBilin U := by
    apply hc.unique_continuousLinearEquivOfBilin
    intro V
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact (hU V).symm
  calc
    U = hc.continuousLinearEquivOfBilin.symm (hc.continuousLinearEquivOfBilin U) :=
      (hc.continuousLinearEquivOfBilin.symm_apply_apply U).symm
    _ = hc.continuousLinearEquivOfBilin.symm ((canonicalMetricValue φ).adjoint g) := by rw [he]
    _ = canonicalResolventH1 φ ht g := rfl

theorem centeredResolvent_integral_eq_zero (d : SourceData μ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    (∫ x, canonicalResolvent d.potential ht g x ∂potentialMeasure d.potential) = 0 := by
  letI := d.source_probability
  exact canonicalMetricValue_integral_eq_zero d.source_C1.continuous _

theorem centeredResolvent_one_eq_zero (d : SourceData μ) {t : ℝ} (ht : 0 < t) :
    letI := d.source_probability
    canonicalResolvent d.potential ht (CenteredL2.oneLp (potentialMeasure d.potential)) = 0 := by
  letI := d.source_probability
  have hU : (0 : CanonicalMetricH1 d.potential) = canonicalResolventH1 d.potential ht
      (CenteredL2.oneLp (potentialMeasure d.potential)) := by
    apply centeredResolvent_unique
    intro V
    simp only [map_zero, inner_zero_left, zero_apply, mul_zero, zero_add]
    rw [CenteredL2.inner_oneLp, canonicalMetricValue_integral_eq_zero d.source_C1.continuous V]
  change canonicalMetricValue d.potential (canonicalResolventH1 d.potential ht
    (CenteredL2.oneLp (potentialMeasure d.potential))) = 0
  rw [← hU, map_zero]

theorem centeredResolvent_center (d : SourceData μ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    letI := d.source_probability
    canonicalResolvent d.potential ht (CenteredL2.center (potentialMeasure d.potential) g) =
      canonicalResolvent d.potential ht g := by
  letI := d.source_probability
  simp [CenteredL2.center, centeredResolvent_one_eq_zero d ht]

/-- Actual source BL improves the centered contraction to 1/(1+t). -/
theorem centeredResolvent_norm_le (d : SourceData μ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    ‖canonicalResolvent d.potential ht g‖ ≤ (1 + t)⁻¹ * ‖g‖ := by
  let U := canonicalResolventH1 d.potential ht g
  have hp := sourceMetricValue_norm_sq_le_energy d U
  have he := canonicalResolvent_energy_identity d.potential ht g
  rw [canonicalMetricEnergy_self] at he
  have hi := real_inner_le_norm g (canonicalResolvent d.potential ht g)
  change ‖canonicalResolvent d.potential ht g‖ ^ 2 ≤
    ∑ i : Fin n, ‖canonicalMetricGradient d.potential i U‖ ^ 2 at hp
  have hpos : 0 < 1 + t := by linarith
  by_cases hz : ‖canonicalResolvent d.potential ht g‖ = 0
  · rw [hz]
    positivity
  · have hn := lt_of_le_of_ne (norm_nonneg (canonicalResolvent d.potential ht g)) (Ne.symm hz)
    apply (le_inv_mul_iff₀ hpos).mpr
    nlinarith [mul_le_mul_of_nonneg_left hp ht.le]

/-- Conservative full resolvent: its constant component is the actual mean. -/
def sourceConservativeResolvent (d : SourceData μ) {t : ℝ} (ht : 0 < t) :
    Lp ℝ 2 (potentialMeasure d.potential) →L[ℝ] Lp ℝ 2 (potentialMeasure d.potential) :=
  letI := d.source_probability
  weightedMassProjection d.potential + canonicalResolvent d.potential ht

theorem sourceConservativeResolvent_apply (d : SourceData μ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    letI := d.source_probability
    sourceConservativeResolvent d ht g = weightedMassProjection d.potential g +
      canonicalResolvent d.potential ht g := rfl

theorem sourceConservativeResolvent_symmetric (d : SourceData μ) {t : ℝ} (ht : 0 < t)
    (f g : Lp ℝ 2 (potentialMeasure d.potential)) :
    inner ℝ (sourceConservativeResolvent d ht f) g =
      inner ℝ f (sourceConservativeResolvent d ht g) := by
  letI := d.source_probability
  rw [sourceConservativeResolvent_apply, sourceConservativeResolvent_apply,
    inner_add_left, inner_add_right, weightedMassProjection_symmetric,
    canonicalResolvent_symmetric]

theorem sourceConservativeResolvent_ae (d : SourceData μ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    (sourceConservativeResolvent d ht g : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      fun x => (∫ y, g y ∂potentialMeasure d.potential) + canonicalResolvent d.potential ht g x := by
  letI := d.source_probability
  rw [sourceConservativeResolvent_apply, weightedMassProjection_apply]
  filter_upwards [Lp.coeFn_add ((∫ y, g y ∂potentialMeasure d.potential) •
      CenteredL2.oneLp (potentialMeasure d.potential)) (canonicalResolvent d.potential ht g),
    Lp.coeFn_smul (∫ y, g y ∂potentialMeasure d.potential)
      (CenteredL2.oneLp (potentialMeasure d.potential)),
    CenteredL2.oneLp_ae (potentialMeasure d.potential)] with x hx hy hz
  simp only [hx, Pi.add_apply, hy, Pi.smul_apply, smul_eq_mul, hz, mul_one]

theorem sourceConservativeResolvent_integral (d : SourceData μ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    (∫ x, sourceConservativeResolvent d ht g x ∂potentialMeasure d.potential) =
      ∫ x, g x ∂potentialMeasure d.potential := by
  letI := d.source_probability
  rw [← CenteredL2.inner_oneLp, sourceConservativeResolvent_apply, inner_add_right,
    weightedMassProjection_apply, inner_smul_right, CenteredL2.inner_oneLp,
    CenteredL2.integral_oneLp, mul_one, CenteredL2.inner_oneLp,
    centeredResolvent_integral_eq_zero d ht g, add_zero]

theorem sourceConservativeResolvent_one (d : SourceData μ) {t : ℝ} (ht : 0 < t) :
    letI := d.source_probability
    sourceConservativeResolvent d ht (CenteredL2.oneLp (potentialMeasure d.potential)) =
      CenteredL2.oneLp (potentialMeasure d.potential) := by
  letI := d.source_probability
  rw [sourceConservativeResolvent_apply, centeredResolvent_one_eq_zero d ht, add_zero,
    weightedMassProjection_apply, CenteredL2.integral_oneLp, one_smul]

theorem center_sourceConservativeResolvent (d : SourceData μ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    letI := d.source_probability
    CenteredL2.center (potentialMeasure d.potential) (sourceConservativeResolvent d ht g) =
      canonicalResolvent d.potential ht (CenteredL2.center (potentialMeasure d.potential) g) := by
  letI := d.source_probability
  rw [CenteredL2.center, sourceConservativeResolvent_integral d ht g,
    sourceConservativeResolvent_apply, weightedMassProjection_apply,
    centeredResolvent_center d ht g]
  abel

theorem sourceConservativeResolvent_norm_le (d : SourceData μ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    ‖sourceConservativeResolvent d ht g‖ ≤ ‖g‖ := by
  letI := d.source_probability
  have ho : inner ℝ (weightedMassProjection d.potential g)
      (CenteredL2.center (potentialMeasure d.potential) g) = 0 := by
    rw [weightedMassProjection_apply, inner_smul_left, CenteredL2.inner_oneLp,
      CenteredL2.integral_center, mul_zero]
  have hr : inner ℝ (weightedMassProjection d.potential g) (canonicalResolvent d.potential ht g) = 0 := by
    rw [weightedMassProjection_apply, inner_smul_left, CenteredL2.inner_oneLp,
      centeredResolvent_integral_eq_zero d ht g, mul_zero]
  have hg : weightedMassProjection d.potential g + CenteredL2.center (potentialMeasure d.potential) g = g := by
    rw [weightedMassProjection_apply, CenteredL2.center]
    abel
  have hgn := norm_add_sq_real (weightedMassProjection d.potential g)
    (CenteredL2.center (potentialMeasure d.potential) g)
  rw [hg, ho, mul_zero, add_zero] at hgn
  have hrn := norm_add_sq_real (weightedMassProjection d.potential g) (canonicalResolvent d.potential ht g)
  rw [← sourceConservativeResolvent_apply, hr, mul_zero, add_zero] at hrn
  have hb := canonicalResolvent_norm_le d.potential ht (CenteredL2.center (potentialMeasure d.potential) g)
  rw [centeredResolvent_center d ht g] at hb
  nlinarith [norm_nonneg (canonicalResolvent d.potential ht g),
    norm_nonneg (CenteredL2.center (potentialMeasure d.potential) g),
    norm_nonneg g, norm_nonneg (sourceConservativeResolvent d ht g)]

/-- On the centered subspace, the actual shifted resolvent has norm at most 1/2. -/
theorem sourceConservativeResolvent_center_half (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    letI := d.source_probability
    ‖CenteredL2.center (potentialMeasure d.potential)
      (sourceConservativeResolvent d (t := 1) zero_lt_one g)‖ ≤
        (1 / 2 : ℝ) * ‖CenteredL2.center (potentialMeasure d.potential) g‖ := by
  letI := d.source_probability
  rw [center_sourceConservativeResolvent]
  simpa only [one_add_one_eq_two, one_div] using
    centeredResolvent_norm_le d (t := 1) zero_lt_one
      (CenteredL2.center (potentialMeasure d.potential) g)

end KLSConstantImprovement.ActualSourceConservativeResolvent405

#print axioms KLSConstantImprovement.ActualSourceConservativeResolvent405.centeredResolvent_unique
#print axioms KLSConstantImprovement.ActualSourceConservativeResolvent405.centeredResolvent_norm_le
#print axioms KLSConstantImprovement.ActualSourceConservativeResolvent405.sourceConservativeResolvent_symmetric
#print axioms KLSConstantImprovement.ActualSourceConservativeResolvent405.sourceConservativeResolvent_integral
#print axioms KLSConstantImprovement.ActualSourceConservativeResolvent405.sourceConservativeResolvent_one
#print axioms KLSConstantImprovement.ActualSourceConservativeResolvent405.sourceConservativeResolvent_norm_le
#print axioms KLSConstantImprovement.ActualSourceConservativeResolvent405.sourceConservativeResolvent_center_half

import KLSConstantImprovement.ActualSourceFamilyBLFilter405
import KLS.ProbabilityMeanCentering

/-!
Exact full conservative resolvent forcing on the same actual source.
The mean term is retained. The actual BL-filter estimate then gives the
finite-entry forcing upper bound, with the actual form-defect energies.
Constant matrix congruences commute by linearity of this constructed scalar
operator. No support projection changes the source variables or diffusion.
-/

noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators ContDiff RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceResolventForcing405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph ActualCanonicalMetricResolvent
open ActualSourceConservativeResolvent405 ActualSourceBLFilter405 ActualSourceFamilyBLFilter405
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_full_resolvent_forcing_identity (d : SourceData μ)
    (f g : Lp ℝ 2 (potentialMeasure d.potential)) :
    letI := d.source_probability
    2 * inner ℝ (sourceConservativeResolvent d (t := 1) zero_lt_one f) g =
      inner ℝ f g + (∫ x, f x ∂potentialMeasure d.potential) *
        (∫ x, g x ∂potentialMeasure d.potential) -
      inner ℝ (CenteredL2.center (potentialMeasure d.potential) f)
        (CenteredL2.center (potentialMeasure d.potential) g - (2 : ℝ) •
          canonicalResolvent d.potential (t := 1) zero_lt_one
            (CenteredL2.center (potentialMeasure d.potential) g)) := by
  letI := d.source_probability
  let m := weightedMassProjection d.potential
  let c := CenteredL2.center (potentialMeasure d.potential)
  have hsplit (h : Lp ℝ 2 (potentialMeasure d.potential)) : h = m h + c h := by
    dsimp [m, c]
    rw [weightedMassProjection_apply, CenteredL2.center]
    abel
  have horth (a b : Lp ℝ 2 (potentialMeasure d.potential)) : inner ℝ (m a) (c b) = 0 := by
    dsimp [m, c]
    rw [weightedMassProjection_apply, inner_smul_left, CenteredL2.inner_oneLp,
      CenteredL2.integral_center, mul_zero]
  have horthR (a b : Lp ℝ 2 (potentialMeasure d.potential)) :
      inner ℝ (m a) (canonicalResolvent d.potential (t := 1) zero_lt_one b) = 0 := by
    dsimp [m]
    rw [weightedMassProjection_apply, inner_smul_left, CenteredL2.inner_oneLp,
      centeredResolvent_integral_eq_zero d zero_lt_one b, mul_zero]
  have hmm : inner ℝ (m f) (m g) = (∫ x, f x ∂potentialMeasure d.potential) *
      (∫ x, g x ∂potentialMeasure d.potential) := by
    dsimp [m]
    rw [weightedMassProjection_apply, inner_smul_left, CenteredL2.inner_oneLp,
      weightedMassProjection_apply]
    have hint : (∫ x, ((∫ y, g y ∂potentialMeasure d.potential) •
        CenteredL2.oneLp (potentialMeasure d.potential)) x ∂potentialMeasure d.potential) =
        ∫ y, g y ∂potentialMeasure d.potential := by
      rw [← CenteredL2.inner_oneLp, inner_smul_right,
        CenteredL2.inner_oneLp, CenteredL2.integral_oneLp, mul_one]
    rw [hint]
    simp only [starRingEnd_apply, star_trivial]
  have hfg : inner ℝ f g = inner ℝ (m f) (m g) + inner ℝ (c f) (c g) := by
    conv_lhs => rw [hsplit f, hsplit g]
    rw [inner_add_left, inner_add_right, inner_add_right,
      horth f g, real_inner_comm (m g) (c f), horth g f]
    ring
  have hRfg : inner ℝ (sourceConservativeResolvent d (t := 1) zero_lt_one f) g =
      inner ℝ (m f) (m g) + inner ℝ (c f)
        (canonicalResolvent d.potential (t := 1) zero_lt_one (c g)) := by
    rw [sourceConservativeResolvent_apply]
    change inner ℝ (m f + canonicalResolvent d.potential (t := 1) zero_lt_one f) g = _
    conv_lhs => rw [hsplit g]
    rw [inner_add_left, inner_add_right, inner_add_right,
      horth f g, real_inner_comm (m g) (canonicalResolvent d.potential (t := 1) zero_lt_one f),
      horthR g f, ← centeredResolvent_center d zero_lt_one f,
      canonicalResolvent_symmetric]
    ring
  rw [hRfg, hfg, hmm, inner_sub_right, inner_smul_right]
  change 2 * (_ + _) = _ + _ + _ - (_ - 2 * _)
  ring

theorem actual_family_resolvent_forcing_upper (d : SourceData μ)
    {ι : Type*} [Fintype ι]
    (f g : ι → Lp ℝ 2 (potentialMeasure d.potential))
    (U V : ι → CanonicalMetricH1 d.potential)
    (hU : ∀ i, canonicalMetricValue d.potential (U i) =
      letI := d.source_probability; CenteredL2.center (potentialMeasure d.potential) (f i))
    (hV : ∀ i, canonicalMetricValue d.potential (V i) =
      letI := d.source_probability; CenteredL2.center (potentialMeasure d.potential) (g i)) :
    2 * (∑ i, inner ℝ (sourceConservativeResolvent d (t := 1) zero_lt_one (f i)) (g i)) ≤
      (∑ i, inner ℝ (f i) (g i)) +
      (∑ i, (∫ x, f i x ∂potentialMeasure d.potential) * (∫ x, g i x ∂potentialMeasure d.potential)) +
      Real.sqrt ((∑ i, sourceBLDefect d (U i) (U i)) *
        (∑ i, sourceBLDefect d (V i) (V i))) / 2 := by
  letI := d.source_probability
  have hid (i : ι) := actual_full_resolvent_forcing_identity d (f i) (g i)
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ => hid i)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  have hb := actual_family_filter_cross_half d U V
  simp_rw [hU, hV] at hb
  have hneg := neg_le_abs (∑ i, inner ℝ (CenteredL2.center (potentialMeasure d.potential) (f i))
    (CenteredL2.center (potentialMeasure d.potential) (g i) - (2 : ℝ) •
      canonicalResolvent d.potential (t := 1) zero_lt_one
        (CenteredL2.center (potentialMeasure d.potential) (g i))))
  linarith

/-- The scalar full generator is unchanged by constant row congruences. -/
theorem conservativeResolvent_constant_congruence (d : SourceData μ)
    (C : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin n → Fin n → Lp ℝ 2 (potentialMeasure d.potential)) (i j : Fin n) :
    sourceConservativeResolvent d (t := 1) zero_lt_one
      (∑ a, ∑ b, (C i a * C j b) • F a b) =
      ∑ a, ∑ b, (C i a * C j b) •
        sourceConservativeResolvent d (t := 1) zero_lt_one (F a b) := by
  simp only [map_sum, map_smul]

end KLSConstantImprovement.ActualSourceResolventForcing405

#print axioms KLSConstantImprovement.ActualSourceResolventForcing405.actual_full_resolvent_forcing_identity
#print axioms KLSConstantImprovement.ActualSourceResolventForcing405.actual_family_resolvent_forcing_upper
#print axioms KLSConstantImprovement.ActualSourceResolventForcing405.conservativeResolvent_constant_congruence

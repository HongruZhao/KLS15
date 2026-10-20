import KLSConstantImprovement.ActualCompactSignedWeakBound405
import KLSConstantImprovement.ActualTargetCutoffErrorBudget405

/-! A literal coordinate of the actual metric inverse is controlled by
the square-root natural-mass excess.  This pays the compact signed L2
positive-part estimate used in the weak limit, with no bounded-mass input. -/
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ENNReal BigOperators
namespace KLSConstantImprovement.ActualSignedCoordinateExcess405
open KLS ActualBoundedCanonicalSource ActualDensityWeightedL2405 ActualCompactDensityHalf405
open ActualCompactSignedWeakBound405 ActualSourceLocalizedGaffney405 ActualSourceNaturalGaffney405
open ActualSourceBoundedMassCutoffs405 ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricInverse
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ} {μ : Measure (Space n)}

def naturalMassExcess (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (B : ℝ) (x : Space n) : ℝ :=
  max (Real.sqrt (sourceVectorMass d.potential (naturalCanonicalFlux d g) x) - B) 0

theorem actual_metric_gradient_signed_le_sqrt_mass (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (i : Fin n)
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      s * canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g) x ≤
        Real.sqrt (sourceVectorMass d.potential (naturalCanonicalFlux d g) x) := by
  filter_upwards [naturalCanonicalMass_square_ae d g] with x hx
  have hM : 0 ≤ sourceVectorMass d.potential (naturalCanonicalFlux d g) x := by
    rw [← hx]
    exact Finset.sum_nonneg fun a _ => sq_nonneg _
  have hsq : canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g) x ^ 2 ≤
      sourceVectorMass d.potential (naturalCanonicalFlux d g) x := by
    rw [← hx]
    exact Finset.single_le_sum
      (fun a _ => sq_nonneg (canonicalMetricGradient d.potential a (sourceMetricInverseH1 d g) x))
      (Finset.mem_univ i)
  have hab : |canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g) x| ≤
      Real.sqrt (sourceVectorMass d.potential (naturalCanonicalFlux d g) x) := by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    simpa only [sq_abs, Real.sq_sqrt hM] using hsq
  rcases hs with rfl | rfl
  · simpa only [one_mul] using (le_abs_self _).trans hab
  · simpa only [neg_one_mul] using (neg_le_abs _).trans hab

theorem actual_signed_compact_residual_norm_sq_le_cutoff_excess
    (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (E : Set (Space n)) (hE : IsCompact E) (i : Fin n) (s B : ℝ)
    (hs : s = 1 ∨ s = -1) (χ : Space n → ℝ)
    (hχ : ∀ x, x ∈ E → χ x = 1)
    (hI : Integrable (fun x => χ x ^ 2 * naturalMassExcess d g B x ^ 2)
      (potentialMeasure d.potential)) :
    ‖Lp.posPart (signedCompactResidual d.potential d.source_C1.continuous E hE
      (toVolumeL2 d.source_C1.continuous
        (canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g))) s B)‖ ^ 2 ≤
      ∫ x, χ x ^ 2 * naturalMassExcess d g B x ^ 2 ∂potentialMeasure d.potential := by
  let q := canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g)
  let r := signedCompactResidual d.potential d.source_C1.continuous E hE
    (toVolumeL2 d.source_C1.continuous q) s B
  have hcoef := toVolumeL2_ae d.source_C1.continuous q
  have hres := signedCompactResidual_ae d.potential d.source_C1.continuous E hE
    (toVolumeL2 d.source_C1.continuous q) s B
  have hsign := (actual_metric_gradient_signed_le_sqrt_mass d g i s hs).filter_mono
    (volume_absolutelyContinuous_potentialMeasure d.source_C1.continuous).ae_le
  have hdom : ∀ᵐ x ∂(volume : Measure (Space n)),
      Lp.posPart r x ^ 2 ≤
        (χ x ^ 2 * naturalMassExcess d g B x ^ 2) * Real.exp (-d.potential x) := by
    filter_upwards [Lp.coeFn_posPart r, hcoef, hres, hsign] with x hp hq hr hx
    change (Lp.posPart r x) ^ 2 ≤ _
    rw [hp]
    change max (r x) 0 ^ 2 ≤ _
    rw [show r x = E.indicator
      (fun y => s * toVolumeL2 d.source_C1.continuous q y - B * densityHalf d.potential y) x from hr]
    by_cases hxE : x ∈ E
    · rw [indicator_of_mem hxE, hq]
      have hρ : 0 ≤ densityHalf d.potential x := Real.exp_nonneg _
      have hm : max (s * q x - B) 0 ≤ naturalMassExcess d g B x :=
        max_le_max (sub_le_sub_right hx B) le_rfl
      have he : s * (densityHalf d.potential x * q x) - B * densityHalf d.potential x =
          densityHalf d.potential x * (s * q x - B) := by ring
      rw [he, ← mul_zero (densityHalf d.potential x), ← mul_max_of_nonneg _ _ hρ]
      have hbound := mul_le_mul_of_nonneg_left hm hρ
      have hsq : (densityHalf d.potential x * max (s * q x - B) 0) ^ 2 ≤
          (densityHalf d.potential x * naturalMassExcess d g B x) ^ 2 :=
        (sq_le_sq₀ (mul_nonneg hρ (le_max_right _ _))
          (mul_nonneg hρ (le_max_right _ _))).mpr hbound
      rw [hχ x hxE, one_pow, one_mul]
      calc
        _ ≤ (densityHalf d.potential x * naturalMassExcess d g B x) ^ 2 := hsq
        _ = _ := by rw [mul_pow, densityHalf_square]; ring
    · rw [indicator_of_notMem hxE, max_self, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      positivity
  have hi := (integrable_potentialMeasure_iff d.source_C1.continuous.measurable).mp hI
  rw [L2.norm_sq_eq_integral_sq, integral_potentialMeasure d.source_C1.continuous.measurable]
  exact integral_mono_ae (Lp.memLp (Lp.posPart r)).integrable_sq hi hdom

end KLSConstantImprovement.ActualSignedCoordinateExcess405
#print axioms KLSConstantImprovement.ActualSignedCoordinateExcess405.actual_metric_gradient_signed_le_sqrt_mass
#print axioms KLSConstantImprovement.ActualSignedCoordinateExcess405.actual_signed_compact_residual_norm_sq_le_cutoff_excess

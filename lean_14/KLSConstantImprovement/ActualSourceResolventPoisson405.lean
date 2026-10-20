import KLSConstantImprovement.ActualSourceClosedGenerator405

/-!
The actual full unit resolvent is a natural Poisson solution with the
literal forcing g-R1g. Its mean and norm bounds are paid from the
constructed conservative resolvent. This transfers the natural Poisson
regularity theorem to R1H without a compact strong operator core.
-/
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped BigOperators ContDiff Topology RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceResolventPoisson405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualCanonicalMetricResolvent ActualWeakCanonicalMetricInverse
open ActualSourceConservativeResolvent405 ActualSourceClosedGenerator405
variable {n : ℕ} {μ : Measure (Space n)}

theorem sourceResolventForcing_integral_zero (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    (∫ x, (g - sourceConservativeResolvent d (t := 1) zero_lt_one g) x
      ∂potentialMeasure d.potential) = 0 := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  rw [← CenteredL2.inner_oneLp, inner_sub_right, CenteredL2.inner_oneLp,
    CenteredL2.inner_oneLp, sourceConservativeResolvent_integral d zero_lt_one g, sub_self]

theorem sourceResolventH1_eq_inverse_forcing (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    canonicalResolventH1 d.potential (t := 1) zero_lt_one g =
      sourceMetricInverseH1 d (g - sourceConservativeResolvent d (t := 1) zero_lt_one g) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  apply sourceMetricInverse_unique d
  intro V
  have hfull : inner ℝ (sourceConservativeResolvent d (t := 1) zero_lt_one g)
      (canonicalMetricValue d.potential V) =
      inner ℝ (canonicalResolvent d.potential (t := 1) zero_lt_one g)
        (canonicalMetricValue d.potential V) := by
    rw [sourceConservativeResolvent_apply, inner_add_left, weightedMassProjection_apply,
      inner_smul_left, CenteredL2.inner_oneLp,
      canonicalMetricValue_integral_eq_zero d.source_C1.continuous V, mul_zero, zero_add]
  have he := canonicalResolvent_variational d.potential (t := 1) zero_lt_one g V
  rw [inner_sub_left, hfull]
  linarith

theorem sourceResolventForcing_norm_sq_le (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    ‖g - sourceConservativeResolvent d (t := 1) zero_lt_one g‖ ^ 2 ≤ ‖g‖ ^ 2 := by
  let R := sourceConservativeResolvent d (t := 1) zero_lt_one g
  have hp : 0 ≤ inner ℝ (g - R) R := by
    dsimp only [R]
    rw [generator_resolvent_energy_identity, canonicalMetricEnergy_self]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have he := norm_sub_sq_real g R
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at hp
  change ‖g - R‖ ^ 2 ≤ ‖g‖ ^ 2
  nlinarith [sq_nonneg ‖R‖]

end KLSConstantImprovement.ActualSourceResolventPoisson405

#print axioms KLSConstantImprovement.ActualSourceResolventPoisson405.sourceResolventForcing_integral_zero
#print axioms KLSConstantImprovement.ActualSourceResolventPoisson405.sourceResolventH1_eq_inverse_forcing
#print axioms KLSConstantImprovement.ActualSourceResolventPoisson405.sourceResolventForcing_norm_sq_le

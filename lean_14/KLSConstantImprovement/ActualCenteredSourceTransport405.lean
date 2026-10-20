import KLSConstantImprovement.ActualSourceCentering405

/-! The centered potentials used in source compactness retain the original
actual moment law after their proved partition normalization. Neither
normalization nor the transported law is an input certificate. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal
namespace KLSConstantImprovement.ActualCenteredSourceTransport405
open KLS ActualBoundedCanonicalSource ActualSourceCentering405
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem centeredSourcePotential_partition (d : SourceData μ) :
    momentPartitionFunction (centeredSourcePotential d) =
      Real.exp (d.potential (actualSourceMinimum d)) := by
  rw [centeredSourcePotential, momentPartitionFunction_normalizeAt,
    actual_source_partition_eq_one, mul_one]

theorem centeredSourcePotential_exp_integrable (d : SourceData μ) :
    Integrable (fun x => Real.exp (-centeredSourcePotential d x)) volume := by
  by_contra h
  have hz : momentPartitionFunction (centeredSourcePotential d) = 0 := integral_undef h
  rw [centeredSourcePotential_partition] at hz
  exact Real.exp_ne_zero _ hz

theorem centeredSourcePotential_transport_pairing (d : SourceData μ)
    (v : BoundedContinuousFunction (Space n) ℝ) :
    (∫ x, v (gradient (normalizedMomentPotential (centeredSourcePotential d)) x)
      ∂potentialMeasure (normalizedMomentPotential (centeredSourcePotential d))) =
        ∫ y, v y ∂μ := by
  have hψc : Continuous (normalizedMomentPotential (centeredSourcePotential d)) :=
    (centeredSourcePotential_C1 d).continuous.add_const _
  rw [integral_potentialMeasure hψc.measurable]
  simp_rw [gradient_normalizedMomentPotential]
  change (∫ x, v (gradient (normalizeMomentPotentialAt d.potential (actualSourceMinimum d)) x) *
    Real.exp (-normalizedMomentPotential (centeredSourcePotential d) x)) = _
  simp_rw [gradient_normalizeAt, centeredSourcePotential_normalized]
  rw [integral_add_right_eq_self (fun x : Space n =>
    v (gradient d.potential x) * Real.exp (-d.potential x)) (actualSourceMinimum d)]
  rw [← integral_potentialMeasure d.source_C1.continuous.measurable]
  have hm : (potentialMeasure d.potential).map (gradient d.potential) = μ := d.pushforward
  calc
    _ = ∫ y, v y ∂(potentialMeasure d.potential).map (gradient d.potential) :=
      (integral_map (measurable_gradient _).aemeasurable v.continuous.aestronglyMeasurable).symm
    _ = _ := congrArg (fun ρ : Measure (Space n) => ∫ y, v y ∂ρ) hm

theorem centeredSourcePotential_pushforward (d : SourceData μ) :
    (potentialMeasure (normalizedMomentPotential (centeredSourcePotential d))).map
      (gradient (normalizedMomentPotential (centeredSourcePotential d))) = μ := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  letI : IsProbabilityMeasure μ := by
    constructor
    rw [← d.pushforward]
    change ((potentialMeasure d.potential).map (gradient d.potential)) Set.univ = 1
    rw [Measure.map_apply (measurable_gradient _) MeasurableSet.univ]
    simp
  letI := isProbabilityMeasure_normalizedMomentPotential (centeredSourcePotential_exp_integrable d)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro v
  rw [integral_map (measurable_gradient _).aemeasurable v.continuous.aestronglyMeasurable]
  exact centeredSourcePotential_transport_pairing d v

end KLSConstantImprovement.ActualCenteredSourceTransport405
#print axioms KLSConstantImprovement.ActualCenteredSourceTransport405.centeredSourcePotential_exp_integrable
#print axioms KLSConstantImprovement.ActualCenteredSourceTransport405.centeredSourcePotential_transport_pairing
#print axioms KLSConstantImprovement.ActualCenteredSourceTransport405.centeredSourcePotential_pushforward

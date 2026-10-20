import KLSConstantImprovement.ActualCubic404894545OfMassBounds
import KLSConstantImprovement.OriginalCubic405Endpoint

/-! End-to-end original-law transfer for the tightened scalar production cap.
The actual existential mass source is the already proved unconditional405 gate. -/
noncomputable section
open MeasureTheory Matrix Filter ProbabilityTheory
open scoped BigOperators
namespace KLSConstantImprovement.OriginalCubic404894545
open KLS ActualBoundedCanonicalSource ActualBoundedStrongCubicVarianceReduction
open ActualCubicSourceDatum405 ActualCubicRepresenter ActualSourceNaturalGaffney405
open ActualSourceLocalizedGaffney405 ActualSourceQuadraticEta405 ActualDeficitTensorBounds
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
theorem boundedStrong_raw404894545_of_mass_source_gate (hMass : OriginalCubic405MassSourceGate.BoundedStrongMassSourceGate405) :
    BoundedStrongLiteralCubicVarianceBound (404894545/1000000) := by
  intro n μ hμ hreg T h12 h23
  letI : IsProbabilityMeasure μ := hμ.isProb
  by_cases hn : 1 ≤ n
  · obtain ⟨d, CQ, CP, hCQ, hCP, hMQ, hMP⟩ := hMass hn hμ hreg T h12 h23
    exact (ActualCubic404894545OfMassBounds.actual_raw404894545_of_mass_bounds d hn hμ T h12 h23 hCQ hCP hMQ hMP).2
  · have hn0 : n = 0 := by omega
    subst n
    have hp : tensorPolynomial μ T = fun _ => (0 : ℝ) := by
      funext x
      simp [ActualCubicRepresenter.tensorPolynomial]
    have hs : tensorSquare T = 0 := by
      simp [tensorSquare, KLSBelow25.CubicSymmetricNoise.square,
        KLSBelow25.CubicSymmetricNoise.tripleSum]
    rw [hp, hs]
    change variance (0 : Space 0 → ℝ) μ ≤ (404894545/1000000:ℝ) * 0
    rw [ProbabilityTheory.variance_zero]
    norm_num

theorem original_literal_raw404894545_of_mass_source_gate (hMass : OriginalCubic405MassSourceGate.BoundedStrongMassSourceGate405) :
    LiteralCubicVarianceObservationTransfer.UniversalLiteralCubicVarianceBound (404894545/1000000) :=
  original_literal_raw_cap_of_boundedStrong_class (by norm_num)
    (boundedStrong_raw404894545_of_mass_source_gate hMass)

theorem original_observation_raw404894545_of_mass_source_gate (hMass : OriginalCubic405MassSourceGate.BoundedStrongMassSourceGate405) :
    RawCubicWeightedBudget.UniversalRawCubicBound (404894545/1000000) :=
  original_raw_observation_bound_of_boundedStrong_class (by norm_num)
    (boundedStrong_raw404894545_of_mass_source_gate hMass)

theorem original_literal_raw404894545 :
    LiteralCubicVarianceObservationTransfer.UniversalLiteralCubicVarianceBound (404894545/1000000) :=
  original_literal_raw404894545_of_mass_source_gate OriginalCubic405Endpoint.actual_mass_source_gate405

theorem original_observation_raw404894545 :
    RawCubicWeightedBudget.UniversalRawCubicBound (404894545/1000000) :=
  original_observation_raw404894545_of_mass_source_gate OriginalCubic405Endpoint.actual_mass_source_gate405

end KLSConstantImprovement.OriginalCubic404894545
#print axioms KLSConstantImprovement.OriginalCubic404894545.boundedStrong_raw404894545_of_mass_source_gate
#print axioms KLSConstantImprovement.OriginalCubic404894545.original_literal_raw404894545
#print axioms KLSConstantImprovement.OriginalCubic404894545.original_observation_raw404894545

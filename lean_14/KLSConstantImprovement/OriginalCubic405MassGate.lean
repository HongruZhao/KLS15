import KLSConstantImprovement.ActualCubic405OfMassBounds
import KLSConstantImprovement.ActualBoundedStrongCubicVarianceReduction

/-! Exact remaining analytic gate for original-law cubic405. This file
proves the transfer from the gate, and does not assert the gate itself.
It introduces no axiom, realization witness or additional law restriction. -/
noncomputable section
open MeasureTheory Matrix Filter ProbabilityTheory
open scoped BigOperators
namespace KLSConstantImprovement.OriginalCubic405MassGate
open KLS ActualBoundedCanonicalSource ActualCubic405OfMassBounds
open ActualBoundedStrongCubicVarianceReduction ActualCubicSourceDatum405 ActualCubicRepresenter
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405 ActualSourceQuadraticEta405 ActualDeficitTensorBounds
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def ActualQuadraticCubicMassGate405 : Prop :=
  ∀ {n : ℕ} {μ : Measure (Space n)} (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j),
    ∃ CQ CP : ℝ, 0 ≤ CQ ∧ 0 ≤ CP ∧
      (∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
        sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ CQ) ∧
      ∀ᵐ x ∂potentialMeasure d.potential,
        sourceVectorMass d.potential (naturalCanonicalFlux d (actualCubicDatum d T)) x ≤ CP

theorem boundedStrong_raw405_of_mass_gate (hMass : ActualQuadraticCubicMassGate405) :
    BoundedStrongLiteralCubicVarianceBound 405 := by
  intro n μ hμ hreg T h12 h23
  letI : IsProbabilityMeasure μ := hμ.isProb
  by_cases hn : 1 ≤ n
  · obtain ⟨d⟩ := exists_sourceData hμ hreg
    obtain ⟨CQ, CP, hCQ, hCP, hMQ, hMP⟩ := hMass hn hμ d T h12 h23
    exact (actual_raw405_of_mass_bounds d hn hμ T h12 h23 hCQ hCP hMQ hMP).2
  · have hn0 : n = 0 := by omega
    subst n
    have hp : tensorPolynomial μ T = fun _ => (0 : ℝ) := by
      funext x
      simp [ActualCubicRepresenter.tensorPolynomial]
    have hs : tensorSquare T = 0 := by
      simp [tensorSquare, KLSBelow25.CubicSymmetricNoise.square,
        KLSBelow25.CubicSymmetricNoise.tripleSum]
    rw [hp, hs]
    change variance (0 : Space 0 → ℝ) μ ≤ 405 * 0
    rw [ProbabilityTheory.variance_zero]
    norm_num

theorem original_literal_raw405_of_mass_gate (hMass : ActualQuadraticCubicMassGate405) :
    LiteralCubicVarianceObservationTransfer.UniversalLiteralCubicVarianceBound 405 :=
  original_literal_raw_cap_of_boundedStrong_class (by norm_num)
    (boundedStrong_raw405_of_mass_gate hMass)

theorem original_observation_raw405_of_mass_gate (hMass : ActualQuadraticCubicMassGate405) :
    RawCubicWeightedBudget.UniversalRawCubicBound 405 :=
  original_raw_observation_bound_of_boundedStrong_class (by norm_num)
    (boundedStrong_raw405_of_mass_gate hMass)

end KLSConstantImprovement.OriginalCubic405MassGate
#print axioms KLSConstantImprovement.OriginalCubic405MassGate.boundedStrong_raw405_of_mass_gate
#print axioms KLSConstantImprovement.OriginalCubic405MassGate.original_literal_raw405_of_mass_gate
#print axioms KLSConstantImprovement.OriginalCubic405MassGate.original_observation_raw405_of_mass_gate

import KLSConstantImprovement.OriginalCubic405MassGate

/-! The sufficient analytic gate needs one actual source for each original
bounded strongly convex law and tensor. It does not require a uniqueness
theorem comparing all source realizations. This module only proves the
exact original-law implication; it does not assert the mass-source gate. -/
noncomputable section
open MeasureTheory Matrix Filter ProbabilityTheory
open scoped BigOperators
namespace KLSConstantImprovement.OriginalCubic405MassSourceGate
open KLS ActualBoundedCanonicalSource ActualCubic405OfMassBounds
open ActualBoundedStrongCubicVarianceReduction ActualCubicSourceDatum405 ActualCubicRepresenter
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405 ActualSourceQuadraticEta405 ActualDeficitTensorBounds
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def BoundedStrongMassSourceGate405 : Prop :=
  ∀ {n : ℕ} {μ : Measure (Space n)} (hn : 1 ≤ n) (hμ : admissibleMeasure μ),
    HasSmoothBoundedStronglyConvexDensity μ →
    ∀ (T : Fin n → Matrix (Fin n) (Fin n) ℝ),
      (∀ i j k, T i j k = T j i k) → (∀ i j k, T i j k = T i k j) →
    ∃ (d : SourceData μ) (CQ CP : ℝ), 0 ≤ CQ ∧ 0 ≤ CP ∧
      (∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
        sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ CQ) ∧
      ∀ᵐ x ∂potentialMeasure d.potential,
        sourceVectorMass d.potential (naturalCanonicalFlux d (actualCubicDatum d T)) x ≤ CP

theorem mass_source_gate_of_all_source_mass
    (hMass : OriginalCubic405MassGate.ActualQuadraticCubicMassGate405) :
    BoundedStrongMassSourceGate405 := by
  intro n μ hn hμ hreg T h12 h23
  obtain ⟨d⟩ := exists_sourceData hμ hreg
  obtain ⟨CQ, CP, hCQ, hCP, hMQ, hMP⟩ := hMass hn hμ d T h12 h23
  exact ⟨d, CQ, CP, hCQ, hCP, hMQ, hMP⟩

theorem boundedStrong_raw405_of_mass_source_gate (hMass : BoundedStrongMassSourceGate405) :
    BoundedStrongLiteralCubicVarianceBound 405 := by
  intro n μ hμ hreg T h12 h23
  letI : IsProbabilityMeasure μ := hμ.isProb
  by_cases hn : 1 ≤ n
  · obtain ⟨d, CQ, CP, hCQ, hCP, hMQ, hMP⟩ := hMass hn hμ hreg T h12 h23
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

theorem original_literal_raw405_of_mass_source_gate (hMass : BoundedStrongMassSourceGate405) :
    LiteralCubicVarianceObservationTransfer.UniversalLiteralCubicVarianceBound 405 :=
  original_literal_raw_cap_of_boundedStrong_class (by norm_num)
    (boundedStrong_raw405_of_mass_source_gate hMass)

theorem original_observation_raw405_of_mass_source_gate (hMass : BoundedStrongMassSourceGate405) :
    RawCubicWeightedBudget.UniversalRawCubicBound 405 :=
  original_raw_observation_bound_of_boundedStrong_class (by norm_num)
    (boundedStrong_raw405_of_mass_source_gate hMass)

end KLSConstantImprovement.OriginalCubic405MassSourceGate
#print axioms KLSConstantImprovement.OriginalCubic405MassSourceGate.mass_source_gate_of_all_source_mass
#print axioms KLSConstantImprovement.OriginalCubic405MassSourceGate.boundedStrong_raw405_of_mass_source_gate
#print axioms KLSConstantImprovement.OriginalCubic405MassSourceGate.original_literal_raw405_of_mass_source_gate
#print axioms KLSConstantImprovement.OriginalCubic405MassSourceGate.original_observation_raw405_of_mass_source_gate

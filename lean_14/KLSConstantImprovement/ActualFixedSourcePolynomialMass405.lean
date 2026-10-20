import KLSConstantImprovement.ActualFixedSourceBoundedForcingMass405
import KLSConstantImprovement.ActualTargetExtensionDatumBinding405
import KLSConstantImprovement.ActualCubicQuadraticRegression

/-! Bounded compact C1 forcing mass on one fixed actual source supplies
exactly the quadratic-row and original cubic mass bounds used by raw405.
Every extension is centered by the original law, and the final source is
retained for all rows and for the cubic datum. This module does not assert
the bounded-forcing mass premise. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff BigOperators
namespace KLSConstantImprovement.ActualFixedSourcePolynomialMass405
open KLS ActualBoundedCanonicalSource ActualCompactTargetExtensions405
open ActualTargetExtensionDatumBinding405 ActualSourceQuadraticEta405
open ActualCubicSourceDatum405 ActualCubicGradientEnergy ActualCubicRepresenter
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem fixed_source_quadratic_cubic_mass_of_bounded_forcing
    (d : SourceData μ) (hμ : admissibleMeasure μ)
    (hMass : ∀ (F : Space n → ℝ) (hF : ContDiff ℝ 1 F), HasCompactSupport F →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂potentialMeasure d.potential,
        sourceVectorMass d.potential
          (naturalCanonicalFlux d (centeredTargetDatum d F hF.continuous)) x ≤ M)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    ∃ CQ CP : ℝ, 0 ≤ CQ ∧ 0 ≤ CP ∧
      (∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
        sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ CQ) ∧
      ∀ᵐ x ∂potentialMeasure d.potential,
        sourceVectorMass d.potential (naturalCanonicalFlux d (actualCubicDatum d T)) x ≤ CP := by
  have hrow (i : Fin n) : ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ M := by
    have hf : ContDiff ℝ 1
        (fun y : Space n => ActualCubicGradientEnergy.centeredQuadratic (T i) y / 2) :=
      ((ActualCubicQuadraticRegression.centeredQuadratic_contDiff (T i)).of_le (by simp)).div_const 2
    obtain ⟨F, _C, _G, hF, hcF, _hC, _hG, heq, _hbF, _hbG⟩ :=
      exists_compact_C1_target_extension hf d.target_bounded
    obtain ⟨M, hM, hb⟩ := hMass F hF hcF
    rw [centeredTargetDatum_eq_quadraticSourceDatum d hμ (T i) hF.continuous heq] at hb
    exact ⟨M, hM, hb⟩
  choose MQ hMQ hrowBound using hrow
  have hf : ContDiff ℝ 1 (tensorPolynomial μ T) :=
    (tensorPolynomial_contDiff μ T).of_le (by simp)
  obtain ⟨F, _C, _G, hF, hcF, _hC, _hG, heq, _hbF, _hbG⟩ :=
    exists_compact_C1_target_extension hf d.target_bounded
  obtain ⟨CP, hCP, hMP⟩ := hMass F hF hcF
  rw [centeredTargetDatum_eq_actualCubicDatum d hμ T hF.continuous heq] at hMP
  refine ⟨∑ i, MQ i, CP, Finset.sum_nonneg (fun i _ => hMQ i), hCP, ?_, hMP⟩
  intro i
  exact (hrowBound i).mono fun _ hx => hx.trans
    (Finset.single_le_sum (fun j _ => hMQ j) (Finset.mem_univ i))

end KLSConstantImprovement.ActualFixedSourcePolynomialMass405
#print axioms KLSConstantImprovement.ActualFixedSourcePolynomialMass405.fixed_source_quadratic_cubic_mass_of_bounded_forcing

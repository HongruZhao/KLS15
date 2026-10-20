import KLSConstantImprovement.ActualNaturalGradientForm405
import KLSConstantImprovement.ActualCubicSourceDatum405
import KLSConstantImprovement.ActualSourceQuadraticEta405
import KLSConstantImprovement.ActualSourceVariationalFlux405

/-! The actual cubic variance pairs directly with its own Poisson
Hessian through the genuine quadratic eta rows. This avoids an
all-forcing scalar response theorem. Only the cubic mass gate remains
as a hypothesis in this constructed variational factorization. -/
noncomputable section
open MeasureTheory Matrix InnerProductSpace Filter ProbabilityTheory
open scoped BigOperators
namespace KLSConstantImprovement.ActualCubicRowVariational405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualCubicRepresenter ActualCubicGradientEnergy ActualCubicSourceDatum405
open ActualNaturalGradientForm405 ActualSourceQuadraticEta405 ActualSourceVariationalFlux405
open ActualSourceNaturalTargetCurvatureDomain405 ActualSourceNaturalWhitenedHessian405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405 ActualCompactRawMetricGraph
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_quadratic_eta_gradient_test (d : SourceData μ) (hμ : admissibleMeasure μ)
    (B : Matrix (Fin n) (Fin n) ℝ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (i : Fin n)
    (U : CanonicalMetricH1 d.potential)
    (hU : (canonicalMetricValue d.potential U : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      (fun x => naturalCanonicalRawGradient d g i x -
        ∫ y, naturalCanonicalRawGradient d g i y ∂potentialMeasure d.potential)) :
    canonicalMetricEnergy d.potential (quadraticSourceEta d B) U =
      (1 / 2 : ℝ) * ∫ x, naturalCanonicalRawGradient d g i x *
        ActualCubicGradientEnergy.centeredQuadratic B (gradient d.potential x) ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hh := quadraticSourceEta_variational d B U
  rw [weighted_inner_centered_test (naturalCanonicalRawGradient_memLp d g i) hU,
    quadraticSourceDatum_mean_zero d hμ B, zero_mul, sub_zero] at hh
  rw [hh]
  calc
    _ = ∫ x, (1 / 2 : ℝ) * (naturalCanonicalRawGradient d g i x *
        ActualCubicGradientEnergy.centeredQuadratic B (gradient d.potential x))
        ∂potentialMeasure d.potential := by
      apply integral_congr_ae
      filter_upwards [quadraticSourceDatum_ae d B] with x hx
      rw [hx]
      ring
    _ = _ := integral_const_mul _ _

theorem exists_actual_cubic_row_variational_of_mass_bound (d : SourceData μ)
    (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (actualCubicDatum d T)) x ≤ C) :
    ∃ Du : Fin n → Fin n → Space n → ℝ,
      (∀ a b, MemLp (fun x => naturalWhitenedHessian d (actualCubicDatum d T) Du x a b) 2
        (potentialMeasure d.potential)) ∧
      (∫ x, matrixFrobeniusSq (naturalWhitenedHessian d (actualCubicDatum d T) Du x)
        ∂potentialMeasure d.potential) ≤ variance (tensorPolynomial μ T) μ ∧
      ∃ U : Fin n → CanonicalMetricH1 d.potential,
        (∀ i r, (canonicalMetricGradient d.potential r (U i) : Space n → ℝ)
          =ᵐ[potentialMeasure d.potential] rawCanonicalMetricDerivative d.potential
            (fun a x => ActualSourceNaturalHessian405.naturalCanonicalHessian d (actualCubicDatum d T) Du x i a) r) ∧
        variance (tensorPolynomial μ T) μ =
          6 * ∑ i, canonicalMetricEnergy d.potential (quadraticSourceEta d (T i)) (U i) := by
  let g := actualCubicDatum d T
  obtain ⟨Du, hW, _, hb, U, hUv, hUd⟩ := exists_natural_gradient_forms_of_mass_bound d hn g
    (actualCubicDatum_mean_zero d hμ T) hC hM
  refine ⟨Du, hW, ?_, U, hUd, ?_⟩
  · rwa [actualCubicDatum_norm_sq d hμ T] at hb
  · have hv := actual_cubic_self_variational d hμ T hT12 hT23
    have hi (i : Fin n) : Integrable (fun x => naturalCanonicalRawGradient d g i x *
        ActualCubicGradientEnergy.centeredQuadratic (T i) (gradient d.potential x))
        (potentialMeasure d.potential) :=
      (naturalCanonicalRawGradient_memLp d g i).integrable_mul
        (d.continuous_comp_gradient_memLp
          ((contDiff_matrixQuadratic (T i)).sub contDiff_const).continuous 2)
    rw [integral_finsetSum Finset.univ (fun i _ => hi i)] at hv
    have hs : (∑ i, canonicalMetricEnergy d.potential (quadraticSourceEta d (T i)) (U i)) =
        (1 / 2 : ℝ) * ∑ i, ∫ x, naturalCanonicalRawGradient d g i x *
          ActualCubicGradientEnergy.centeredQuadratic (T i) (gradient d.potential x)
            ∂potentialMeasure d.potential := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => actual_quadratic_eta_gradient_test d hμ (T i) g i (U i) (hUv i)
    change _ = 3 * ∑ i, ∫ x, naturalCanonicalRawGradient d g i x *
      ActualCubicGradientEnergy.centeredQuadratic (T i) (gradient d.potential x)
        ∂potentialMeasure d.potential at hv
    linarith

end KLSConstantImprovement.ActualCubicRowVariational405
#print axioms KLSConstantImprovement.ActualCubicRowVariational405.actual_quadratic_eta_gradient_test
#print axioms KLSConstantImprovement.ActualCubicRowVariational405.exists_actual_cubic_row_variational_of_mass_bound

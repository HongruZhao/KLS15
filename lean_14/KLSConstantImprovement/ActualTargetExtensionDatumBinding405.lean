import KLSConstantImprovement.ActualCompactTargetExtensions405
import KLSConstantImprovement.ActualSourceQuadraticEta405
import KLSConstantImprovement.ActualCubicSourceDatum405

/-! The fixed bounded extensions used on growing targets become exactly
the original quadratic and cubic source data on the final original law.
The equality is an equality in the genuine source L2 space, paid by the
actual pushforward and the true target support. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualTargetExtensionDatumBinding405
open KLS ActualBoundedCanonicalSource ActualCompactTargetExtensions405
open ActualSourceQuadraticEta405 ActualCubicSourceDatum405
open ActualCubicGradientEnergy ActualCubicRepresenter ActualCubicAffineRegression
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem target_functions_ae_eq_of_eqOn (d : SourceData μ)
    {F f : Space n → ℝ} (heq : ∀ y ∈ d.targetSet, F y = f y) : F =ᵐ[μ] f := by
  rw [d.target_representation]
  filter_upwards [ae_restrict_mem d.target_closed.measurableSet] with y hy
  exact heq y hy

theorem centeredTargetDatum_eq_actual_pullback_of_extension
    (d : SourceData μ) {F f : Space n → ℝ} (hF : Continuous F) (hf : Continuous f)
    (heq : ∀ y ∈ d.targetSet, F y = f y) (hm : (∫ y, f y ∂μ) = 0) :
    centeredTargetDatum d F hF =
      (d.continuous_comp_gradient_memLp hf 2).toLp (fun x => f (gradient d.potential x)) := by
  have ht : F =ᵐ[μ] f := target_functions_ae_eq_of_eqOn d heq
  have hmF : (∫ y, F y ∂μ) = 0 := (integral_congr_ae ht).trans hm
  have hs : (fun x => F (gradient d.potential x)) =ᵐ[potentialMeasure d.potential]
      (fun x => f (gradient d.potential x)) :=
    d.gradient_measurePreserving.quasiMeasurePreserving.ae_eq_comp ht
  apply Lp.ext
  filter_upwards [centeredTargetDatum_ae d F hF,
    (d.continuous_comp_gradient_memLp hf 2).coeFn_toLp, hs] with x hx hy hz
  rw [hx, hy, hz, hmF, sub_zero]

theorem centeredTargetDatum_eq_quadraticSourceDatum
    (d : SourceData μ) (hμ : admissibleMeasure μ) (B : Matrix (Fin n) (Fin n) ℝ)
    {F : Space n → ℝ} (hF : Continuous F)
    (heq : ∀ y ∈ d.targetSet, F y = ActualCubicGradientEnergy.centeredQuadratic B y/2) :
    centeredTargetDatum d F hF = quadraticSourceDatum d B := by
  have hf : Continuous (fun y : Space n => ActualCubicGradientEnergy.centeredQuadratic B y/2) :=
    (((contDiff_matrixQuadratic B).sub contDiff_const).div_const 2).continuous
  have hm : (∫ y, ActualCubicGradientEnergy.centeredQuadratic B y/2 ∂μ) = 0 := by
    rw [integral_div, centeredQuadratic_mean_zero hμ B, zero_div]
  exact centeredTargetDatum_eq_actual_pullback_of_extension d hF hf heq hm

theorem centeredTargetDatum_eq_actualCubicDatum
    (d : SourceData μ) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    {F : Space n → ℝ} (hF : Continuous F)
    (heq : ∀ y ∈ d.targetSet, F y = tensorPolynomial μ T y) :
    centeredTargetDatum d F hF = actualCubicDatum d T :=
  centeredTargetDatum_eq_actual_pullback_of_extension d hF
    (tensorPolynomial_contDiff μ T).continuous heq (tensorPolynomial_centered hμ T)

end KLSConstantImprovement.ActualTargetExtensionDatumBinding405
#print axioms KLSConstantImprovement.ActualTargetExtensionDatumBinding405.target_functions_ae_eq_of_eqOn
#print axioms KLSConstantImprovement.ActualTargetExtensionDatumBinding405.centeredTargetDatum_eq_actual_pullback_of_extension
#print axioms KLSConstantImprovement.ActualTargetExtensionDatumBinding405.centeredTargetDatum_eq_quadraticSourceDatum
#print axioms KLSConstantImprovement.ActualTargetExtensionDatumBinding405.centeredTargetDatum_eq_actualCubicDatum

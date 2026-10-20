import KLSConstantImprovement.ActualGlobalRawFormTest405
import KLSConstantImprovement.ActualCubicGradientEnergy

/-! The literal original cubic is an actual centered source datum. Its
natural inverse satisfies the global polynomial variational identity.
No Hessian-domain or bounded-inverse-mass premise is used here. -/
noncomputable section
open MeasureTheory Matrix InnerProductSpace Filter ProbabilityTheory
open scoped BigOperators
namespace KLSConstantImprovement.ActualCubicSourceDatum405
open KLS ActualBoundedCanonicalSource ActualCubicRepresenter ActualCubicGradientEnergy
open ActualGlobalRawFormTest405 ActualSourceNaturalTargetCurvatureDomain405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

def actualCubicDatum (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    Lp ℝ 2 (potentialMeasure d.potential) :=
  (d.continuous_comp_gradient_memLp (tensorPolynomial_contDiff μ T).continuous 2).toLp
    (fun x => tensorPolynomial μ T (gradient d.potential x))

theorem actualCubicDatum_coe (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (actualCubicDatum d T : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      fun x => tensorPolynomial μ T (gradient d.potential x) :=
  (d.continuous_comp_gradient_memLp (tensorPolynomial_contDiff μ T).continuous 2).coeFn_toLp

theorem actualCubicDatum_mean_zero (d : SourceData μ) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (∫ x, actualCubicDatum d T x ∂potentialMeasure d.potential) = 0 := by
  rw [integral_congr_ae (actualCubicDatum_coe d T),
    d.integral_comp_gradient (tensorPolynomial_contDiff μ T).continuous]
  exact tensorPolynomial_centered hμ T

theorem actualCubicDatum_norm_sq (d : SourceData μ) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    ‖actualCubicDatum d T‖ ^ 2 = variance (tensorPolynomial μ T) μ := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  rw [L2.norm_sq_eq_integral_sq]
  calc
    _ = ∫ x, tensorPolynomial μ T (gradient d.potential x) ^ 2 ∂potentialMeasure d.potential :=
      integral_congr_ae (by
        filter_upwards [actualCubicDatum_coe d T] with x hx
        exact congrArg (fun z : ℝ => z ^ 2) hx)
    _ = ∫ x, tensorPolynomial μ T x ^ 2 ∂μ :=
      d.integral_comp_gradient ((tensorPolynomial_contDiff μ T).continuous.pow 2)
    _ = _ := by
      rw [variance_eq_integral (tensorPolynomial_memLp hμ T).aemeasurable, tensorPolynomial_centered hμ T]
      simp only [sub_zero]

theorem actual_cubic_natural_variational (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0) :
    (∫ x, g x * tensorPolynomial μ T (gradient d.potential x) ∂potentialMeasure d.potential) =
      3 * ∫ x, ∑ i, naturalCanonicalRawGradient d g i x *
        ActualCubicGradientEnergy.centeredQuadratic (T i) (gradient d.potential x) ∂potentialMeasure d.potential := by
  have hp := actual_target_pullback_variational d g ((tensorPolynomial_contDiff μ T).of_le (by simp))
  rw [hg, zero_mul, sub_zero] at hp
  have he (x : Space n) : (∑ i, naturalCanonicalRawGradient d g i x *
      gradient (tensorPolynomial μ T) (gradient d.potential x) i) =
      3 * ∑ i, naturalCanonicalRawGradient d g i x * ActualCubicGradientEnergy.centeredQuadratic (T i) (gradient d.potential x) := by
    simp_rw [← coordinateDerivative_eq_gradient, tensorPolynomial_derivative μ T hT12 hT23]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [integral_congr_ae (Eventually.of_forall he), integral_const_mul] at hp
  exact hp.symm

theorem actual_cubic_self_variational (d : SourceData μ) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j) :
    variance (tensorPolynomial μ T) μ =
      3 * ∫ x, ∑ i, naturalCanonicalRawGradient d (actualCubicDatum d T) i x *
        ActualCubicGradientEnergy.centeredQuadratic (T i) (gradient d.potential x) ∂potentialMeasure d.potential := by
  have hp := actual_cubic_natural_variational d T hT12 hT23 (actualCubicDatum d T)
    (actualCubicDatum_mean_zero d hμ T)
  have he : (∫ x, actualCubicDatum d T x * tensorPolynomial μ T (gradient d.potential x)
      ∂potentialMeasure d.potential) = ‖actualCubicDatum d T‖ ^ 2 := by
    rw [L2.norm_sq_eq_integral_sq]
    apply integral_congr_ae
    filter_upwards [actualCubicDatum_coe d T] with x hx
    rw [hx]
    ring
  rwa [he, actualCubicDatum_norm_sq d hμ T] at hp

end KLSConstantImprovement.ActualCubicSourceDatum405
#print axioms KLSConstantImprovement.ActualCubicSourceDatum405.actualCubicDatum_mean_zero
#print axioms KLSConstantImprovement.ActualCubicSourceDatum405.actualCubicDatum_norm_sq
#print axioms KLSConstantImprovement.ActualCubicSourceDatum405.actual_cubic_natural_variational
#print axioms KLSConstantImprovement.ActualCubicSourceDatum405.actual_cubic_self_variational

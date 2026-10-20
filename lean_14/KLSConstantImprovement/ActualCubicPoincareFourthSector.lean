import KLSConstantImprovement.ActualCubicGradientEnergy
import KLSConstantImprovement.CubicVarianceFourthSector

/-! The current unconditional Poincare endpoint pays the low-fourth sector of
the literal cubic variance on every original admissible law. This is used to
weaken a remaining high-sector curvature requirement; no curvature estimate
is asserted here. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal ContDiff
namespace KLSConstantImprovement.ActualCubicPoincareFourthSector
open KLS KLS.DeterministicBridge KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise
open ActualDeficitTensorBounds ActualCubicRepresenter ActualCubicGradientEnergy
open CubicVarianceFourthSector ActualCubicVarianceIdentity ActualFixedTensorDeficit
variable {n : ℕ}
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

theorem centeredQuadratic_memLp {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (H : Matrix (Fin n) (Fin n) ℝ) : MemLp (ActualCubicGradientEnergy.centeredQuadratic H) 2 μ := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  exact (memLp_matrixQuadratic_of_coordinateProducts
    hμ.quadraticVarianceEight_unconditional.memLp_coordinate_mul H).sub (memLp_const _)

theorem integral_centeredQuadratic_sq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (H : Matrix (Fin n) (Fin n) ℝ) :
    (∫ x,(ActualCubicGradientEnergy.centeredQuadratic H x)^2 ∂μ)=ProbabilityTheory.variance (matrixQuadratic H) μ := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hQ := memLp_matrixQuadratic_of_coordinateProducts
    hμ.quadraticVarianceEight_unconditional.memLp_coordinate_mul H
  rw [ProbabilityTheory.variance_eq_integral hQ.aemeasurable,
    isotropic_integral_matrixQuadratic hμ.isotropic]
  rfl

theorem sum_centeredQuadratic_integrals {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) :
    (∑ i,∫ x,(ActualCubicGradientEnergy.centeredQuadratic (T i) x)^2 ∂μ)=fourthContraction μ T+2*tensorSquare T := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hv (i : Fin n) : (∫ x,(ActualCubicGradientEnergy.centeredQuadratic (T i) x)^2 ∂μ)=
      (∑ a,∑ b,T i a b*actualFourthCumulantFlat μ (T i) a b)+
        2*matrixFrobeniusSq (T i) := by
    rw [integral_centeredQuadratic_sq hμ]
    have hp := actualFourthCumulantFlat_pairing_eq_variance_sub_two
      hμ.quadraticVarianceEight_unconditional (T i)
    linarith
  simp_rw [hv]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←tensorSquare_eq_sum_slices]
  rfl

theorem tensorPolynomial_gradient_norm_sq (μ : Measure (Space n)) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b)
    (x : Space n) :
    ‖gradient (tensorPolynomial μ T) x‖^2=9*(∑ i,(ActualCubicGradientEnergy.centeredQuadratic (T i) x)^2) := by
  rw [EuclideanSpace.real_norm_sq_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [←coordinateDerivative_eq_gradient,tensorPolynomial_derivative μ T hT12 hT23]
  ring

theorem tensorPolynomial_gradient_norm_sq_integrable {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b) :
    Integrable (fun x => ‖gradient (tensorPolynomial μ T) x‖^2) μ := by
  have he : (fun x => ‖gradient (tensorPolynomial μ T) x‖^2)=
      fun x => 9*(∑ i,(ActualCubicGradientEnergy.centeredQuadratic (T i) x)^2) :=
    funext (tensorPolynomial_gradient_norm_sq μ T hT12 hT23)
  rw [he]
  exact (integrable_finsetSum Finset.univ fun i _ =>
    (centeredQuadratic_memLp hμ (T i)).integrable_sq).const_mul 9

theorem tensorPolynomial_gradient_energy {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b) :
    (∫ x,‖gradient (tensorPolynomial μ T) x‖^2 ∂μ)=
      9*(fourthContraction μ T+2*tensorSquare T) := by
  simp_rw [tensorPolynomial_gradient_norm_sq μ T hT12 hT23]
  rw [integral_const_mul,integral_finsetSum Finset.univ (fun i _ =>
    (centeredQuadratic_memLp hμ (T i)).integrable_sq),sum_centeredQuadratic_integrals hμ T]

theorem tensorPolynomial_extended_energy {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b) :
    energy μ (tensorPolynomial μ T)=ENNReal.ofReal (9*(fourthContraction μ T+2*tensorSquare T)) := by
  unfold energy
  rw [←ofReal_integral_eq_lintegral_ofReal
    (tensorPolynomial_gradient_norm_sq_integrable hμ T hT12 hT23)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _),tensorPolynomial_gradient_energy hμ T hT12 hT23]

theorem tensorPolynomial_variance_le_current_poincare {μ : Measure (Space n)}
    (hn : 1≤n) (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ≤
      9*LongPrefixCubicBellmanEndpoint.bound*(fourthContraction μ T+2*tensorSquare T) := by
  have hbound := LongPrefixCubicBellmanEndpoint.original_poincare hn hμ
    (tensorPolynomial_original_test hμ T)
  rw [tensorPolynomial_extended_energy hμ T hT12 hT23] at hbound
  have hright : (280181882107013433/19531250000000000 : ℝ≥0∞)*
      ENNReal.ofReal (9*(fourthContraction μ T+2*tensorSquare T))≠⊤ :=
    ne_of_lt (ENNReal.mul_lt_top (ENNReal.div_lt_top (by norm_num) (by norm_num)) ENNReal.ofReal_lt_top)
  have hr := ENNReal.toReal_mono hright hbound
  change ProbabilityTheory.variance (tensorPolynomial μ T) μ≤_ at hr
  have hE : 0≤9*(fourthContraction μ T+2*tensorSquare T) := by
    rw [←tensorPolynomial_gradient_energy hμ T hT12 hT23]
    exact integral_nonneg fun _ => sq_nonneg _
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hE] at hr
  have hB : (280181882107013433/19531250000000000 : ℝ≥0∞).toReal=
      LongPrefixCubicBellmanEndpoint.bound := by norm_num [LongPrefixCubicBellmanEndpoint.bound]
  rw [hB] at hr
  nlinarith

theorem tensorPolynomial_variance_le_333_low_sector {μ : Measure (Space n)}
    (hn : 1≤n) (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b)
    (hF : fourthContraction μ T≤tensorSquare T/2) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ≤333*tensorSquare T :=
  current_poincare_low_fourth_sector (tensorSquare_nonneg T) hF
    (tensorPolynomial_variance_le_current_poincare hn hμ T hT12 hT23)

theorem tensorPolynomial_variance_le_333_of_high_sector_curvature {μ : Measure (Space n)}
    (hn : 1≤n) (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c=T b a c) (hT23 : ∀ a b c,T a b c=T a c b)
    (hcurvature : tensorSquare T/2<fourthContraction μ T →
      -48*sliceDeficit μ T≤contractedDeficitHessian μ T) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ≤333*tensorSquare T :=
  current_poincare_and_high_sector_curvature_give_333
    (variance_add_deficitHessian_eq hμ T hT12 hT23) (tensorSquare_nonneg T)
    (ActualDeficitBesselBound.signedTraceSquare_bounds_by_fourth_add_two hμ T).2
    (tensorPolynomial_variance_le_current_poincare hn hμ T hT12 hT23) hcurvature

end KLSConstantImprovement.ActualCubicPoincareFourthSector
#print axioms KLSConstantImprovement.ActualCubicPoincareFourthSector.centeredQuadratic_memLp
#print axioms KLSConstantImprovement.ActualCubicPoincareFourthSector.integral_centeredQuadratic_sq
#print axioms KLSConstantImprovement.ActualCubicPoincareFourthSector.sum_centeredQuadratic_integrals
#print axioms KLSConstantImprovement.ActualCubicPoincareFourthSector.tensorPolynomial_gradient_norm_sq
#print axioms KLSConstantImprovement.ActualCubicPoincareFourthSector.tensorPolynomial_gradient_norm_sq_integrable
#print axioms KLSConstantImprovement.ActualCubicPoincareFourthSector.tensorPolynomial_gradient_energy
#print axioms KLSConstantImprovement.ActualCubicPoincareFourthSector.tensorPolynomial_extended_energy
#print axioms KLSConstantImprovement.ActualCubicPoincareFourthSector.tensorPolynomial_variance_le_current_poincare
#print axioms KLSConstantImprovement.ActualCubicPoincareFourthSector.tensorPolynomial_variance_le_333_low_sector
#print axioms KLSConstantImprovement.ActualCubicPoincareFourthSector.tensorPolynomial_variance_le_333_of_high_sector_curvature

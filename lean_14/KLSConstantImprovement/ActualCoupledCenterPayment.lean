import KLSConstantImprovement.CoupledCenterCoercivity
import KLSConstantImprovement.ActualCubic405OfMassBounds

/-! The coupled row/response-center payment is instantiated on the SAME
constructed source and the SAME actual row inverse/Jacobian. All fields
integrated below already have paid global domains under quadratic mass.
No center-domain or new numerical response estimate is assumed. -/
noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators MatrixOrder
namespace KLSConstantImprovement.ActualCoupledCenterPayment
open KLS ActualBoundedCanonicalSource CoupledCenterCoercivity CoupledCenterMetric
open ActualQuadraticCompletedLoss405 ActualQuadraticProductionCompletion405
open ActualQuadraticGramProduction405 ActualQuadraticHessianDomains405
open ActualQuadraticJacobianEnergy405 ActualQuadraticResponseField405 ActualQuadraticHilbertMatrix405
open ActualResponseCoerciveUpper405 ActualResponseProductionState405 ActualResponseGlobalR1Balance405
open ActualResponseGlobalHBalance405 ActualResponseHessianPair405 ActualResponseProductionDomain405
open ActualSourceResponseProduction405 ActualQuadraticResponseMetricFlux405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405 ActualSourceQuadraticEta405
open ActualSourceNaturalHessian405 ActualSourceConnectionFields405 ActualSourceHessianEvolution405
open ActualAffineMatrixTests405 ActualAffineSourceIdentities405 ActualAffineRawBindings405
open ActualAffineResponseHilbert405
open ActualAffineTraceDiscount405 ActualAffineFiniteExpansion405 ActualQuadraticRowCurvature405
open ActualSourceDirectCubicBalance405 ActualSourceCurvatureDomains405 ActualSourceQuarticBinding405
open ActualQuarticThirdWhitening405 ActualQuarticCongruence405 ActualResponseProductionAlgebra405
open ActualFilteredDeficitLimit405 ActualSourceMeanGram405 ActualSourceMatchedDeficit405 ActualDeficitTensorBounds
open ActualSourceMeanGramOrder405
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_coupled_production_ae (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k=T j i k) (h23 : ∀ i j k, T i j k=T i k j) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      (4/3+56/1125:ℝ)*actualDirectMoment d T x-
        (7/400:ℝ)*(actualAffineGamma d T x+2*actualAffineSignedConnection d T x) ≤
      actualResponseXi d hn hμ T x+actualRowCurvature d (quadraticResponseMatrix d T) x+
        actualQuadraticRowLoss d hn hμ T x/2 := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source,d.third_symmetric_ae.filter_mono hac.ae_le,
    ae_all_iff.mpr fun i => (quadraticFluxJacobian_compatible_volume_ae d hn hμ (T i)).filter_mono hac.ae_le,
    ae_all_iff.mpr (actual_quadratic_response_compatible_ae d hn hμ T h12 h23)] with x hx hN hD hDF
  let H := coordinateHessian d.potential x
  let P := sourceTargetCurvature d x
  let U := actualQuadraticFluxMatrix d T x
  let Z := actualAffineMatrix d T x
  let N := sourceThirdMatrix d x
  let D := fun i => quadraticJacobianMatrix d hn hμ (T i) x
  let DF := fun i => responseRowJacobian d hn hμ T i x
  have hTs (i : Fin n) : (T i).IsSymm := Matrix.IsSymm.ext fun a b => h23 i b a
  have hV := coordinateHessian_posSemidef_of_convex (d.target_smooth.of_le (by simp))
    d.target_convex_potential (gradient d.potential x)
  have hP : P.PosSemidef := by
    simpa only [P,sourceTargetCurvature,hx.1.isHermitian.eq] using
      hV.conjTranspose_mul_mul_same (coordinateHessian d.potential x)
  have hUH : H⁻¹*H=1 := Matrix.nonsing_inv_mul H ((Matrix.isUnit_iff_isUnit_det _).mp hx.1.isUnit)
  have hF : quadraticResponseMatrix d T x=(2:ℝ) • U-Z := by
    ext i a
    rfl
  have hRq (i : Fin n) : actualQuadraticResidualFactor d hn hμ T i x=
      completionLeft H H⁻¹ (mixFamily U N i) (D i) (T i) := by
    have hMix : sourceThirdAlong d (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x=
        mixFamily U N i := rfl
    change H⁻¹*(H*D i+sourceThirdAlong d (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x)-T i*H=_
    rw [Matrix.mul_add,←Matrix.mul_assoc,hUH,Matrix.one_mul,hMix]
    rfl
  have hL : rowLossFinite H P U N D T=actualQuadraticRowLoss d hn hμ T x := by
    dsimp only [rowLossFinite,actualQuadraticRowLoss,actualQuadraticTargetRowCost,
      actualQuadraticResidualCost,actualQuadraticJacobianRowCost]
    simp_rw [←hRq]
    rfl
  have hp := coupled_production_pointwise H P U Z hx.1 hP (actualAffineMatrix_symmetric d T hTs x)
    N D DF T (fun i j k => (hN i j k).1) (fun i j k => (hN i j k).2) h12 h23 hD hDF
  rw [hL,←hF] at hp
  dsimp only [H,P,U,Z,N,D,DF] at hp
  have hMixF : mixFamily (quadraticResponseMatrix d T x) (sourceThirdMatrix d x)=
      fun i => sourceThirdAlong d (fun a y => quadraticResponseMatrix d T y i a) x := rfl
  rw [hMixF] at hp
  simpa only [actualDirectMoment,actualAffineGamma,actualAffineSignedConnection,actualResponseXi,
    actualResponseProduction,actualRowCurvature,sourceConnectionCurvature,
    sourceThirdAlong,mixFamily,sourceTargetCurvature,rawGram_eq_matrixTraceGram,Matrix.mul_assoc,
    H,P,U,Z,N,D,DF] using hp

theorem actual_coupled_production (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k=T j i k) (h23 : ∀ i j k, T i j k=T i k j)
    {CQ : ℝ} (hCQ : 0 ≤ CQ)
    (hMQ : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ CQ) :
    (4/3+847/36000:ℝ)*(∫ x,actualDirectMoment d T x ∂potentialMeasure d.potential)+
      (21/800:ℝ)*actualAffineDiscount d T ≤
      (∫ x,actualResponseXi d hn hμ T x ∂potentialMeasure d.potential)+
        (∫ x,actualRowCurvature d (quadraticResponseMatrix d T) x ∂potentialMeasure d.potential)+
          (∫ x,actualQuadraticRowLoss d hn hμ T x ∂potentialMeasure d.potential)/2 := by
  have hTs (i : Fin n) : (T i).IsSymm := Matrix.IsSymm.ext fun a b => h23 i b a
  have hXi := actualResponseXi_integrable d hn hμ T h12 h23 hCQ hMQ
  have hTheta := actual_response_row_curvature_integrable d T hTs hCQ hMQ
  have hL := actualQuadraticRowLoss_integrable d hn hμ T hCQ hMQ
  have hW := actual_direct_moment_integrable d T
  have hGamma := actual_affine_gamma_integrable d T
  have hSigned := actual_affine_signed_integrable d T hTs
  have hleft := (hW.const_mul (4/3+56/1125:ℝ)).sub ((hGamma.add (hSigned.const_mul 2)).const_mul (7/400:ℝ))
  have hright := (hXi.add hTheta).add (hL.div_const 2)
  have hi := integral_mono_ae hleft hright (actual_coupled_production_ae d hn hμ T h12 h23)
  change (∫ x,(4/3+56/1125:ℝ)*actualDirectMoment d T x-
      (7/400:ℝ)*(actualAffineGamma d T x+2*actualAffineSignedConnection d T x) ∂potentialMeasure d.potential) ≤
    (∫ x,actualResponseXi d hn hμ T x+actualRowCurvature d (quadraticResponseMatrix d T) x+
      actualQuadraticRowLoss d hn hμ T x/2 ∂potentialMeasure d.potential) at hi
  have hSub := integral_sub (hW.const_mul (4/3+56/1125:ℝ))
    ((hGamma.add (hSigned.const_mul 2)).const_mul (7/400:ℝ))
  have hSumGamma := integral_add hGamma (hSigned.const_mul 2)
  have hSumRhs := integral_add (hXi.add hTheta) (hL.div_const 2)
  have hSumRhs2 := integral_add hXi hTheta
  simp only [Pi.add_apply,Pi.sub_apply] at hSub hSumGamma hSumRhs hSumRhs2
  rw [hSub,hSumRhs,hSumRhs2,integral_const_mul,integral_const_mul,hSumGamma,
    integral_const_mul,integral_div] at hi
  have hConnection := actual_affine_connection_identity d T hTs
  unfold actualAffineDiscount
  linarith only [hi,hConnection]

theorem actual_response_main_upper_coupled (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k=T j i k) (h23 : ∀ i j k, T i j k=T i k j)
    {CQ : ℝ} (hCQ : 0 ≤ CQ)
    (hMQ : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ CQ) :
    (∫ x,actualResponseMatrixCost d T x ∂potentialMeasure d.potential) ≤
      (1/3-847/72000:ℝ)*(∫ x,actualDirectMoment d T x ∂potentialMeasure d.potential)+
        2*(sourceMeanGram d T).trace+Real.sqrt ((sourceMeanGram d T).trace*(2*tensorSquare T-
          ∫ x,rawHessianTraceSquare (coordinateHessian d.potential x) (CFC.sqrt (sourceCoefficientGram T))
            ∂potentialMeasure d.potential))-
          (∫ x,actualResponseExtra d hn hμ T x ∂potentialMeasure d.potential)+
            (∫ x,actualQuadraticRowLoss d hn hμ T x ∂potentialMeasure d.potential)/4-
              (21/1600:ℝ)*actualAffineDiscount d T := by
  have hs := actual_response_paid_production_state d hn hμ hiso T h12 h23 hCQ hMQ
  have hc := actual_coupled_production d hn hμ T h12 h23 hCQ hMQ
  have hf := actual_fullSymmetric_base_filter_cross_half d hiso T h12 h23
  have hn := neg_le_abs (actualMatrixFilterCross d 1 T)
  linarith only [hs.2.1,hs.2.2,hc,hf,hn]

end KLSConstantImprovement.ActualCoupledCenterPayment
#print axioms KLSConstantImprovement.ActualCoupledCenterPayment.actual_coupled_production_ae
#print axioms KLSConstantImprovement.ActualCoupledCenterPayment.actual_coupled_production
#print axioms KLSConstantImprovement.ActualCoupledCenterPayment.actual_response_main_upper_coupled

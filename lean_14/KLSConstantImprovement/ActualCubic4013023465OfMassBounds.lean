import KLSConstantImprovement.ActualJointProductionPaymentParameter
import KLSConstantImprovement.ProductionParameter4013023465
import KLSConstantImprovement.ActualWholeCubicRow405
import KLSConstantImprovement.ActualResponseCoerciveUpper405
import KLSConstantImprovement.ActualDirectDiskBudget405
import KLSConstantImprovement.ActualSourceDirectCubicCharge405
import KLSConstantImprovement.SourceProductionJointRaw405Payoff

/-! Instantiation of the accepted actual source/row/response inequalities at
the refined rational parameters. Only actual quadratic and cubic inverse mass
estimates are displayed; the original-law wrapper discharges them. -/
noncomputable section
open MeasureTheory Matrix Filter ProbabilityTheory
open scoped BigOperators
namespace KLSConstantImprovement.ActualCubic4013023465OfMassBounds
open KLS ActualBoundedCanonicalSource ActualWholeCubicRow405 ActualResponseCoerciveUpper405
open ActualQuadraticCompletedLoss405 ActualQuadraticHilbertMatrix405 ActualQuadraticResponseField405
open ActualQuadraticRowCurvature405 ActualAffineResponseHilbert405 ActualCubicSourceDatum405 ActualCubicRepresenter
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405 ActualSourceQuadraticEta405
open ActualSourceDirectCubicBalance405 ActualSourceDirectCubicCharge405 ActualDirectDiskBudget405
open ActualAffineTraceDiscount405 ActualAffineSourceIdentities405 ActualAffineGlobalBalance405
open ActualDeficitTensorBounds ActualSourceMeanGram405 ActualResponseProductionState405 ActualResponseGlobalR1Balance405
open SourceProductionJointRaw405Payoff
open ActualCubicMatrixFactorization405 ActualQuadraticRowEll405 ProductionParameter4013023465
open ActualAffineMatrixTests405 ActualCubicHilbertUpper405
open ActualJointProductionPaymentParameter
variable {n : ℕ} {μ : Measure (Space n)}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

theorem actual_raw4013023465_of_mass_bounds (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    {CQ CP : ℝ} (hCQ : 0 ≤ CQ) (hCP : 0 ≤ CP)
    (hMQ : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ CQ)
    (hMP : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (actualCubicDatum d T)) x ≤ CP) :
    variance (tensorPolynomial μ T) μ ≤
      cap * tensorSquare T - (cap / 2) * actualOrientationGap d T -
        affineCredit * actualAffineDiscount d T -
          rowCredit * (∫ x, actualQuadraticRowLoss d hn hμ T x ∂potentialMeasure d.potential) -
            targetCredit * (∫ x, actualAffineTarget d T x ∂potentialMeasure d.potential) -
              extraCredit * (∫ x, actualResponseExtra d hn hμ T x ∂potentialMeasure d.potential) ∧
      variance (tensorPolynomial μ T) μ ≤ cap * tensorSquare T := by
  let V := variance (tensorPolynomial μ T) μ
  let N := tensorSquare T
  let r := actualMean d T
  let t := actualDiskRadiusTerm d T
  let g := actualOrientationGap d T
  let q := actualAffineDiscount d T
  let W := ∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential
  let J := ∫ x, actualAffineMainCost d T x ∂potentialMeasure d.potential
  let MF := ∫ x, actualResponseMatrixCost d T x ∂potentialMeasure d.potential
  let theta := ∫ x, actualRowCurvature d (quadraticResponseMatrix d T) x ∂potentialMeasure d.potential
  let thetaU := ∫ x, actualRowCurvature d (actualQuadraticFluxMatrix d T) x ∂potentialMeasure d.potential
  let thetaZ := ∫ x, actualRowCurvature d (actualAffineMatrix d T) x ∂potentialMeasure d.potential
  let m := ∫ x, actualQuadraticMatrixCost d T x ∂potentialMeasure d.potential
  let ell := ∫ x, actualRowEll d T x ∂potentialMeasure d.potential
  let p := ∫ x, actualAffineTarget d T x ∂potentialMeasure d.potential
  let L := ∫ x, actualQuadraticRowLoss d hn hμ T x ∂potentialMeasure d.potential
  let e := ∫ x, actualResponseExtra d hn hμ T x ∂potentialMeasure d.potential
  have hTs (i : Fin n) : (T i).IsSymm := Matrix.IsSymm.ext fun a b => h23 i b a
  have hqW := actual_affine_discount_bounds d T h12 h23
  have hq : 0 ≤ q := hqW.1
  have hW0 : 0 ≤ W := hqW.1.trans hqW.2
  have hp : 0 ≤ p := actual_affine_target_nonnegative d T hTs
  have hL : 0 ≤ L := integral_nonneg_of_ae (actual_quadratic_row_loss_nonnegative_ae d hn hμ T hTs)
  have hstate := actual_response_paid_production_state d hn hμ hμ.isotropic T h12 h23 hCQ hMQ
  have he : 0 ≤ e := hstate.1
  have hDirect := actual_direct_retained_support d hμ.isotropic T h12 h23
  have hp3 := actual_direct_target_curvature_nonnegative d T hTs
  have hComm := actual_direct_commutator_integral_nonnegative d T
  have hW : W ≤ 3 * (r + t) := by linarith only [hDirect, hp3, hComm]
  have hJ : J ≤ (40555468125569/16785435000000:ℝ)*W-(2500000/3357087:ℝ)*q := by
    have hSquare := actual_affine_integrated_square d T h12 h23 (3357087/5000000)
    have hConnection := actual_affine_connection_identity d T hTs
    have hMain := actual_affine_main_cross_identity d T hTs
    dsimp only [J,W,q]
    unfold actualAffineDiscount
    linarith only [hSquare,hConnection,hMain]
  have hTheta := actual_response_curvature_upper_of_mass_bound d hn hμ hμ.isotropic T h12 h23 hCQ hMQ
  change theta ≤ 2*r+t-e at hTheta
  have hMF := actual_response_main_upper_parameter (k:=1973760870581746440274440635910160403009/3639594487178060976125839596991000000000) d hn hμ hμ.isotropic T h12 h23 (by norm_num) hCQ hMQ
  norm_num at hMF
  change MF ≤ (7279188974356121952251679193982000000000/23811327793650112297029478217856160403009:ℝ)*W+2*r+t-e+(1973760870581746440274440635910160403009/7279188974356121952251679193982000000000:ℝ)*L at hMF
  have hWhole := actual_cubic_variance_le_whole_matrix_of_mass_bound d hn hμ T h12 h23 hCP hMP
  change V ≤ 36*m at hWhole
  have hRow := actual_whole_cubic_row_balance d hn hμ T h12 h23 hCQ hMQ
  change 2*m=W+thetaU+2*ell-L at hRow
  have hThetaU0 : 0 ≤ thetaU := integral_nonneg_of_ae (actual_row_curvature_nonnegative d _)
  have hEllSquare := actualRowEll_integrated_square d T hTs hMQ
  change ell^2 ≤ W*thetaU at hEllSquare
  have hEll := row_ell_parameter hW0 hThetaU0 hEllSquare
  have hSplit := actual_quadratic_row_curvature_split d T hTs hCQ hMQ
  change 2*thetaU ≤ theta+thetaZ at hSplit
  have hAffine := actual_affine_row_curvature_identity d T hTs
  change thetaZ=(W+3*q-2*p)/2 at hAffine
  have hRowUpper := row_branch hWhole hRow hEll hSplit hAffine hTheta hW
  have hVarMain : V ≤ mainJ*J+mainF*MF := by
    obtain ⟨B,hB,hv⟩ := exists_actual_cubic_matrix_pairing_of_mass_bound d hn hμ T h12 h23 hCP hMP
    have hHilbert := six_pairing_split_upper_parameter (actualQuadraticHilbert d T)
      (actualAffineHilbert d T) (actualResponseHilbert d T) B hB hv
      (actual_affine_response_hilbert_split d T)
    rwa [actualAffineHilbert_norm d T hTs,actualResponseHilbert_norm] at hHilbert
  have hMainUpper := main_branch_parameter hVarMain hJ hMF hW
  obtain ⟨_,_,_,hg,hNeff⟩ := actual_disk_nonnegative_and_budget d hμ.isotropic T h12 h23
  have hDisk := actual_matched_scalar_disk d hμ.isotropic T h12 h23
  change 0 ≤ g at hg
  change 0 ≤ N-g/2 at hNeff
  change (r-(N-g/2))^2+t^2=(N-g/2)^2 at hDisk
  exact retained_joint_raw4013023465 hg hNeff (le_of_eq hDisk) hq hp hL he hRowUpper hMainUpper

end KLSConstantImprovement.ActualCubic4013023465OfMassBounds
#print axioms KLSConstantImprovement.ActualCubic4013023465OfMassBounds.actual_raw4013023465_of_mass_bounds

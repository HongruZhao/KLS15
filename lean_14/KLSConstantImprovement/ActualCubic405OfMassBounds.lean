import KLSConstantImprovement.ActualWholeCubicRow405
import KLSConstantImprovement.ActualResponseCoerciveUpper405
import KLSConstantImprovement.ActualDirectDiskBudget405
import KLSConstantImprovement.ActualSourceDirectCubicCharge405
import KLSConstantImprovement.SourceProductionJointRaw405Payoff

/-! Actual cubic405 assembly on the constructed source. All production,
matrix, resolvent, tensor, variance and disk inputs are discharged.
Only the actual quadratic and cubic inverse mass estimates remain
displayed; this is not an unconditional original-law405 theorem. -/
noncomputable section
open MeasureTheory Matrix Filter ProbabilityTheory
open scoped BigOperators
namespace KLSConstantImprovement.ActualCubic405OfMassBounds
open KLS ActualBoundedCanonicalSource ActualWholeCubicRow405 ActualResponseCoerciveUpper405
open ActualQuadraticCompletedLoss405 ActualQuadraticHilbertMatrix405 ActualQuadraticResponseField405
open ActualQuadraticRowCurvature405 ActualAffineResponseHilbert405 ActualCubicSourceDatum405 ActualCubicRepresenter
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405 ActualSourceQuadraticEta405
open ActualSourceDirectCubicBalance405 ActualSourceDirectCubicCharge405 ActualDirectDiskBudget405
open ActualAffineTraceDiscount405 ActualAffineSourceIdentities405 ActualAffineGlobalBalance405
open ActualDeficitTensorBounds ActualSourceMeanGram405 ActualResponseProductionState405 ActualResponseGlobalR1Balance405
open SourceProductionJointRaw405Payoff
variable {n : ℕ} {μ : Measure (Space n)}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

theorem actual_raw405_of_mass_bounds (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    {CQ CP : ℝ} (hCQ : 0 ≤ CQ) (hCP : 0 ≤ CP)
    (hMQ : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ CQ)
    (hMP : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (actualCubicDatum d T)) x ≤ CP) :
    variance (tensorPolynomial μ T) μ ≤
      405 * tensorSquare T - (405 / 2 : ℝ) * actualOrientationGap d T -
        (63 / 625 : ℝ) * actualAffineDiscount d T -
          (108 / 25 : ℝ) * (∫ x, actualQuadraticRowLoss d hn hμ T x ∂potentialMeasure d.potential) -
            (126 / 25 : ℝ) * (∫ x, actualAffineTarget d T x ∂potentialMeasure d.potential) -
              (582 / 25 : ℝ) * (∫ x, actualResponseExtra d hn hμ T x ∂potentialMeasure d.potential) ∧
      variance (tensorPolynomial μ T) μ ≤ 405 * tensorSquare T := by
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
  have hMain := actual_affine_main_discount d T h12 h23
  have hJ : J ≤ (169 / 70 : ℝ) * W - (7 / 10 : ℝ) * q :=
    rational_affine_main_discount hW0 hq hMain
  have hTheta := actual_response_curvature_upper_of_mass_bound d hn hμ hμ.isotropic T h12 h23 hCQ hMQ
  change theta ≤ 2 * r + t - e at hTheta
  have hMF := actual_response_main_upper_of_mass_bound d hn hμ hμ.isotropic T h12 h23 hCQ hMQ
  change MF ≤ W / 3 + 2 * r + t - e at hMF
  have hVarRow := actual_whole_cubic_row_upper_of_mass_bounds d hn hμ T h12 h23 hCQ hCP hMQ hMP
  change V ≤ 42 * W + 21 * theta + (63 / 2 : ℝ) * q - 21 * p - 18 * L at hVarRow
  have hVarMain := actual_cubic_variance_split_of_mass_bound d hn hμ T h12 h23 hCP hMP
  change V ≤ (72 / 5 : ℝ) * J + 24 * MF at hVarMain
  let rowLoss := 21 * p + 18 * L + 21 * e
  let newLoss := 24 * e
  have hRowLoss : 0 ≤ rowLoss := by dsimp only [rowLoss]; positivity
  have hNewLoss : 0 ≤ newLoss := by dsimp only [newLoss]; positivity
  have hRow : V ≤ 168 * r + 147 * t + (63 / 2 : ℝ) * q - rowLoss := by
    dsimp only [rowLoss]
    linarith only [hVarRow, hTheta, hW]
  have hNew : V ≤ (30852 / 175 : ℝ) * r + (26652 / 175 : ℝ) * t -
      (252 / 25 : ℝ) * q - newLoss := by
    dsimp only [newLoss]
    linarith only [hVarMain, hMF, hJ, hW]
  obtain ⟨_, _, _, hg, hNeff⟩ := actual_disk_nonnegative_and_budget d hμ.isotropic T h12 h23
  have hDisk := actual_matched_scalar_disk d hμ.isotropic T h12 h23
  change 0 ≤ g at hg
  change 0 ≤ N - g / 2 at hNeff
  change (r - (N - g / 2)) ^ 2 + t ^ 2 = (N - g / 2) ^ 2 at hDisk
  have hJoint := retained_joint_raw405 hg hNeff (le_of_eq hDisk) hq hRowLoss hNewLoss hRow hNew
  refine ⟨?_, hJoint.2⟩
  change V ≤ 405 * N - (405 / 2 : ℝ) * g - (63 / 625 : ℝ) * q -
    (108 / 25 : ℝ) * L - (126 / 25 : ℝ) * p - (582 / 25 : ℝ) * e
  dsimp only [rowLoss, newLoss] at hJoint
  linarith only [hJoint.1]

end KLSConstantImprovement.ActualCubic405OfMassBounds
#print axioms KLSConstantImprovement.ActualCubic405OfMassBounds.actual_raw405_of_mass_bounds

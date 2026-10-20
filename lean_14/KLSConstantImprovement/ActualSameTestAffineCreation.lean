import KLSConstantImprovement.ActualSameTestAffineCovariance
import KLSConstantImprovement.SameTestAffineTerminalScalar
import KLSConstantImprovement.ActualSameTestCubicCreationCovariance
import KLSConstantImprovement.ActualJointCreationCubicSeed23849Cap

/-! Original-law affine saving for the very same creation test. The first
Appell energy is identified literally with its coordinate covariance.
No terminal charge is discarded here. The following terminal module pays it.
Fresh source draft; compilation belongs to the sole merger. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix InnerProductSpace
open scoped BigOperators ENNReal ContDiff
namespace KLSConstantImprovement.ActualSameTestAffineCreation
open KLS KLS.DeterministicBridge KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25 KLSBelow25.CubicSymmetricNoise KLSBelow25.CubicCreation
open ActualDeficitTensorBounds ActualCubicRepresenter ActualCubicGradientEnergy
open ActualCubicQuadraticRegression ActualCubicQuadraticDeficit
open ActualCubicCreationJointDual ActualDeficitCurvatureConditionalEndpoint
open QuadraticCovarianceCharge ActualSameTestAffineCovariance SameTestAffineTerminalScalar
open OriginalUpperRecovery6SameTestCovarianceDraft
variable {n : ℕ}
set_option maxHeartbeats 5000000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

def affineBaseC : ℝ := 71727/5000
def affineEffectiveC : ℝ := 66727/5000

theorem affineEffectiveC_eq : affineEffectiveC = affineBaseC-1 := by
  norm_num [affineEffectiveC, affineBaseC]

theorem covarianceVector_eq_affineProjectionVector {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) :
    covarianceVector μ f = @affineProjectionVector n μ hμ.isProb hμ.isotropic f := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  ext i
  change (∫ x, x i*f x ∂μ) = inner ℝ (isotropicAffineCoordinate hμ.isotropic (some i)) f
  rw [inner_isotropicAffineCoordinate]
  apply integral_congr_ae (.of_forall fun x => ?_)
  simp only [affineCoordinateFunction, Option.elim_some]

theorem actual_first_energy_eq_covariance_norm {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) :
    actualAppellEnergy μ f 1 = ‖covarianceVector μ f‖^2 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  rw [actualAppellEnergy_eq_norm_sq,
    fullClassAppellTensor_one_norm_sq hμ.logConcave hμ.isotropic,
    covarianceVector_eq_affineProjectionVector hμ f]

theorem actual_unit_first_energy_le_one {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) :
    actualAppellEnergy μ f 1 ≤ 1 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  rw [actualAppellEnergy_eq_norm_sq]
  simpa only [hunit, one_pow] using
    fullClassAppellTensor_one_norm_sq_le hμ.logConcave hμ.isotropic f

theorem actual_mixed_same_test_affine_unit {μ : Measure (Space n)}
    (hn : 1≤n) (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ)
    (hunit : ‖f‖=1) (s : ℝ) :
    (actualAppellEnergy μ f 3-s*(properThirdPairing μ f/3))^2 ≤
      (affineBaseC-actualAppellEnergy μ f 1)*
        (9*(fourthContraction μ (actualCubicNextArray μ f)+
          2*tensorSquare (actualCubicNextArray μ f))+
          (4*s^2-12*s)*matrixFrobeniusSq
            (symmetricAnnihilation μ (actualCubicNextArray μ f))) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hi : (∫ x,(f x)^2 ∂μ)=1 := by
    rw [←actualLp_norm_sq_eq_integral,hunit]
    norm_num
  have hp := original_mixed_same_test_affine_saving hn hμ (actualCubicNextArray μ f)
    (actualCubicNextArray_first_symmetry hμ.logConcave (Lp.memLp f))
    (actualCubicNextArray_last_symmetry hμ.logConcave (Lp.memLp f))
    (symmetricAnnihilation μ (actualCubicNextArray μ f))
    (symmetricAnnihilation_isSymm μ _) s affineBaseC
    (by norm_num [LongPrefixCubicBellmanEndpoint.bound,affineBaseC]) (Lp.memLp f) hi
  rw [actual_mixed_same_test_covariance hμ (Lp.memLp f),
    quadraticGradientPairing_symmetricAnnihilation,
    ←actual_first_energy_eq_covariance_norm hμ f] at hp
  convert hp using 1 <;> ring

theorem actual_creation_same_test_affine_quadratic_unit {μ : Measure (Space n)}
    (hn : 1≤n) (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) (hunit : ‖f‖=1)
    {s : ℝ} (hs0 : 0 ≤ s) (hs3 : s ≤ 3) :
    let X := actualAppellEnergy μ f 3
    let Y := actualAppellEnergy μ f 2
    let c := affineBaseC-actualAppellEnergy μ f 1
    let j := properThirdPairing μ f/3
    (s^2*Y+4*c*s*(3-s))*j^2-2*s*X*Y*j-X*Y*(72*c-X)≤0 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  let X := actualAppellEnergy μ f 3
  let Y := actualAppellEnergy μ f 2
  let c := affineBaseC-actualAppellEnergy μ f 1
  let j := properThirdPairing μ f/3
  let R := matrixFrobeniusSq (symmetricAnnihilation μ (actualCubicNextArray μ f))
  have hr1 := actual_unit_first_energy_le_one hμ f hunit
  have hc : 0<c := by dsimp [c,affineBaseC]; linarith
  have hY : 0≤Y := actualAppellEnergy_nonneg μ f 2
  have hbase := actual_mixed_same_test_affine_unit hn hμ f hunit s
  have hF := (fourthContraction_bounds hμ (actualCubicNextArray μ f)
    (actualCubicNextArray_last_symmetry hμ.logConcave (Lp.memLp f))).2
  unfold tensorSquare at hF hbase
  rw [actualCubicNextArray_square] at hF hbase
  have hpc : (X-s*j)^2 ≤ 72*c*X+4*c*s*(s-3)*R := by
    dsimp only [X,j,R,c]
    have hp := mul_le_mul_of_nonneg_left hF hc.le
    nlinarith [hbase,hp]
  have hs := actual_proper_creation_pairing_sq_le_nine hμ (Lp.memLp f)
  have hj : j^2≤R*Y := by dsimp [j,R,Y,properThirdPairing]; nlinarith [hs]
  have hsign : 4*c*s*(s-3)≤0 := mul_nonpos_of_nonneg_of_nonpos
    (by positivity) (sub_nonpos.mpr hs3)
  have hpaid := mul_le_mul_of_nonneg_right hpc hY
  have hr := mul_le_mul_of_nonpos_left hj hsign
  dsimp only [X, Y, j, R, c] at hpaid hr ⊢
  nlinarith [hpaid,hr]

theorem closed_upper_eq_doubleRatio {c X Y : ℝ} (hc : 0<c) (hX : 0<X) :
    (X*Y+Real.sqrt ((4*c-Y)*X*Y*(72*c-X)))/(2*c) =
      X/2*doubleRatio c X Y := by
  have hid : (4*c-Y)*X*Y*(72*c-X)=(X*c)^2*radical c X Y := by
    unfold radical
    field_simp [hc.ne',hX.ne']
    <;> ring
  rw [hid,Real.sqrt_mul (sq_nonneg (X*c)),Real.sqrt_sq (mul_pos hX hc).le]
  unfold doubleRatio
  field_simp [hc.ne']
  <;> ring

theorem actual_creation_same_test_affine_upper_unit {μ : Measure (Space n)}
    (hn : 1≤n) (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) (hunit : ‖f‖=1)
    (hX : 0<actualAppellEnergy μ f 3) :
    2*properThirdPairing μ f ≤ actualAppellEnergy μ f 3*
      doubleRatio (affineBaseC-actualAppellEnergy μ f 1)
        (actualAppellEnergy μ f 3) (actualAppellEnergy μ f 2) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hr1 := actual_unit_first_energy_le_one hμ f hunit
  have hc : 4<affineBaseC-actualAppellEnergy μ f 1 := by
    norm_num [affineBaseC] at *
    linarith
  have hY8 := actualAppellEnergy_two_le_eight_norm_sq hμ f
  rw [hunit,one_pow,mul_one] at hY8
  have hb := creation_same_test_scalar_upper hc hX.le
    (actualAppellEnergy_nonneg μ f 2) hY8
    (fun s hs0 hs3 => actual_creation_same_test_affine_quadratic_unit hn hμ f hunit hs0 hs3)
  have he := closed_upper_eq_doubleRatio (by linarith : 0<affineBaseC-actualAppellEnergy μ f 1) hX
    (Y:=actualAppellEnergy μ f 2)
  have he' :
      (actualAppellEnergy μ f 3*actualAppellEnergy μ f 2+
        Real.sqrt ((4*(affineBaseC-actualAppellEnergy μ f 1)-actualAppellEnergy μ f 2)*
          actualAppellEnergy μ f 3*actualAppellEnergy μ f 2*
          (72*(affineBaseC-actualAppellEnergy μ f 1)-actualAppellEnergy μ f 3)))/
        (6*(affineBaseC-actualAppellEnergy μ f 1)) =
      actualAppellEnergy μ f 3/6*doubleRatio (affineBaseC-actualAppellEnergy μ f 1)
        (actualAppellEnergy μ f 3) (actualAppellEnergy μ f 2) := by
    calc
      _ = ((actualAppellEnergy μ f 3*actualAppellEnergy μ f 2+
        Real.sqrt ((4*(affineBaseC-actualAppellEnergy μ f 1)-actualAppellEnergy μ f 2)*
          actualAppellEnergy μ f 3*actualAppellEnergy μ f 2*
          (72*(affineBaseC-actualAppellEnergy μ f 1)-actualAppellEnergy μ f 3)))/
        (2*(affineBaseC-actualAppellEnergy μ f 1)))/3 := by
        field_simp [(by linarith : affineBaseC-actualAppellEnergy μ f 1≠0)]
        <;> ring
      _ = _ := by rw [he]; ring
  rw [he'] at hb
  nlinarith [hb]

end KLSConstantImprovement.ActualSameTestAffineCreation
#print axioms KLSConstantImprovement.ActualSameTestAffineCreation.actual_first_energy_eq_covariance_norm
#print axioms KLSConstantImprovement.ActualSameTestAffineCreation.actual_mixed_same_test_affine_unit
#print axioms KLSConstantImprovement.ActualSameTestAffineCreation.actual_creation_same_test_affine_quadratic_unit
#print axioms KLSConstantImprovement.ActualSameTestAffineCreation.actual_creation_same_test_affine_upper_unit

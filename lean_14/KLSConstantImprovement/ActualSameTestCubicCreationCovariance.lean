import KLSConstantImprovement.RefinedPiecewiseCreationEnvelope
import KLS.QuadraticCovarianceOperator

/-! A same-unit original-law covariance bound for full proper creation.
The mixed polynomial is paired with the very same f whose actual coefficient
tensor it uses. This correlation was discarded in the earlier supporting lines.
All identifications are literal, and the final bound is one-sided in the
proper pairing, suitable for the original heat terminal. No build by author.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix InnerProductSpace
open scoped BigOperators ENNReal ContDiff
namespace KLSConstantImprovement.OriginalUpperRecovery6SameTestCovarianceDraft
open KLS KLS.DeterministicBridge KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise KLSBelow25.CubicCreation
open ActualDeficitTensorBounds ActualCubicRepresenter ActualCubicGradientEnergy
open ActualCubicQuadraticRegression ActualCubicQuadraticDeficit
open ActualCubicPoincareFourthSector
open ActualCubicCreationJointDual ActualDeficitCurvatureConditionalEndpoint
open OriginalUpperRecovery6PiecewiseEnvelopeDraft
variable {n : ℕ}
set_option maxHeartbeats 5000000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

def properThirdPairing (μ : Measure (Space n)) (f : Space n → ℝ) : ℝ :=
  actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3

theorem centeredQuadratic_same_test_covariance {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    covariance (ActualCubicGradientEnergy.centeredQuadratic
      (symmetricAnnihilation μ (actualCubicNextArray μ f))) f μ =
      properThirdPairing μ f / 3 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  let K := symmetricAnnihilation μ (actualCubicNextArray μ f)
  have hq := memLp_matrixQuadratic_of_coordinateProducts
    hμ.quadraticVarianceEight_unconditional.memLp_coordinate_mul K
  have he : covariance (ActualCubicGradientEnergy.centeredQuadratic K) f μ =
      ∑ i, ∑ j, K i j * actualAppellCoefficient μ f 2 ![i,j] := by
    rw [covariance_comm]
    unfold ActualCubicGradientEnergy.centeredQuadratic
    rw [covariance_sub_const_right (hq.integrable (by norm_num)),
      covariance_matrixQuadratic_eq_pairing hf hμ.quadraticVarianceEight_unconditional.memLp_coordinate_mul]
    simp_rw [actualAppellCoefficient_two_eq_quadraticCovariance hμ hf]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hp : (∑ i, ∑ j, K i j * actualAppellCoefficient μ f 2 ![i,j]) =
      quadraticGradientPairing μ (actualCubicNextArray μ f)
        (fun i j => actualAppellCoefficient μ f 2 ![i,j]) := by
    unfold quadraticGradientPairing
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [K]
    ring
  rw [he, hp]
  unfold properThirdPairing
  rw [actual_proper_creation_pairing_eq hμ hf]
  ring

theorem actual_mixed_same_test_covariance {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) (s : ℝ) :
    covariance (quadraticPerturbation μ (actualCubicNextArray μ f)
      (symmetricAnnihilation μ (actualCubicNextArray μ f)) s) f μ =
      actualAppellEnergy μ f 3 - s * (properThirdPairing μ f / 3) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  unfold quadraticPerturbation
  rw [covariance_fun_sub_left (tensorPolynomial_memLp hμ (actualCubicNextArray μ f))
    ((centeredQuadratic_memLp hμ
      (symmetricAnnihilation μ (actualCubicNextArray μ f))).const_mul s) hf,
    covariance_const_mul_left,
    coefficientPolynomial_covariance hμ hf, centeredQuadratic_same_test_covariance hμ hf]

theorem actual_mixed_same_test_poincare_unit {μ : Measure (Space n)}
    (hn : 1 ≤ n) (hμ : admissibleMeasure μ) {f : Space n → ℝ}
    (hf : MemLp f 2 μ) (hunit : (∫ x, (f x)^2 ∂μ) = 1) (s : ℝ) :
    (actualAppellEnergy μ f 3 - s * (properThirdPairing μ f / 3))^2 ≤
      supportC * (9*(fourthContraction μ (actualCubicNextArray μ f) +
        2*tensorSquare (actualCubicNextArray μ f)) +
        (4*s^2-12*s)*matrixFrobeniusSq
          (symmetricAnnihilation μ (actualCubicNextArray μ f))) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  let T := actualCubicNextArray μ f
  let K := symmetricAnnihilation μ T
  have hfvar : ProbabilityTheory.variance f μ ≤ 1 := by
    rw [ProbabilityTheory.variance_eq_sub hf]
    change (∫ x, (f x)^2 ∂μ) - (∫ x, f x ∂μ)^2 ≤ 1
    rw [hunit]
    nlinarith [sq_nonneg (∫ x, f x ∂μ)]
  have hmix := (quadraticPerturbation_original_test hμ T K s).2
  have hcs := covariance_sq_le_variance_mul_variance hmix hf
  rw [actual_mixed_same_test_covariance hμ hf] at hcs
  have hpaid := mul_le_mul_of_nonneg_left hfvar
    (ProbabilityTheory.variance_nonneg (quadraticPerturbation μ T K s) μ)
  have hp := quadraticPerturbation_refined_poincare hn hμ T
    (actualCubicNextArray_first_symmetry hμ.logConcave hf)
    (actualCubicNextArray_last_symmetry hμ.logConcave hf) K
    (symmetricAnnihilation_isSymm μ T) s
  rw [quadraticGradientPairing_symmetricAnnihilation] at hp
  rw [← quadraticPerturbation_variance hμ T K s] at hp
  have hpaid' : ProbabilityTheory.variance (quadraticPerturbation μ T K s) μ *
      ProbabilityTheory.variance f μ ≤
      ProbabilityTheory.variance (quadraticPerturbation μ T K s) μ := by
    simpa only [mul_one] using hpaid
  have hb := hcs.trans (hpaid'.trans hp)
  dsimp only [T, K] at hb
  nlinarith [hb]

theorem actual_creation_same_test_quadratic_unit {μ : Measure (Space n)}
    (hn : 1 ≤ n) (hμ : admissibleMeasure μ) {f : Space n → ℝ}
    (hf : MemLp f 2 μ) (hunit : (∫ x, (f x)^2 ∂μ) = 1)
    {s : ℝ} (hs0 : 0 ≤ s) (hs3 : s ≤ 3) :
    let X := actualAppellEnergy μ f 3
    let Y := actualAppellEnergy μ f 2
    let j := properThirdPairing μ f / 3
    (s^2*Y+4*supportC*s*(3-s))*j^2 -
      2*s*X*Y*j - X*Y*(72*supportC-X) ≤ 0 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  let X := actualAppellEnergy μ f 3
  let Y := actualAppellEnergy μ f 2
  let j := properThirdPairing μ f / 3
  let R := matrixFrobeniusSq (symmetricAnnihilation μ (actualCubicNextArray μ f))
  have hC : 0 < supportC := by norm_num [supportC]
  have hY : 0 ≤ Y := actualAppellEnergy_nonneg μ f 2
  have hbase := actual_mixed_same_test_poincare_unit hn hμ hf hunit s
  have hF := (fourthContraction_bounds hμ (actualCubicNextArray μ f)
    (actualCubicNextArray_last_symmetry hμ.logConcave hf)).2
  unfold tensorSquare at hF hbase
  rw [actualCubicNextArray_square] at hF hbase
  have hpc : (X-s*j)^2 ≤ 72*supportC*X + 4*supportC*s*(s-3)*R := by
    dsimp only [X, j, R]
    have hp := mul_le_mul_of_nonneg_left hF hC.le
    nlinarith [hbase, hp]
  have hs := actual_proper_creation_pairing_sq_le_nine hμ hf
  have hj : j^2 ≤ R*Y := by dsimp [j, R, Y, properThirdPairing]; nlinarith [hs]
  have hc : 4*supportC*s*(s-3) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
    (by positivity) (sub_nonpos.mpr hs3)
  have hpaid := mul_le_mul_of_nonneg_right hpc hY
  have hr := mul_le_mul_of_nonpos_left hj hc
  dsimp only [X, Y, j, R] at hpaid hr ⊢
  nlinarith [hpaid, hr]

theorem creation_same_test_scalar_upper {C X Y j : ℝ}
    (hC : 4 < C) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hY8 : Y ≤ 8)
    (hq : ∀ s : ℝ, 0 ≤ s → s ≤ 3 →
      (s^2*Y+4*C*s*(3-s))*j^2-2*s*X*Y*j-X*Y*(72*C-X) ≤ 0) :
    j ≤ (X*Y+Real.sqrt ((4*C-Y)*X*Y*(72*C-X)))/(6*C) := by
  have hCp : 0 < C := by linarith
  have hD : 0 < 4*C-Y := by linarith
  have hXY : 0 ≤ X*Y := mul_nonneg hX hY
  by_cases hb : 6*C*j ≤ X*Y
  · apply (le_div_iff₀ (by positivity : 0 < 6*C)).mpr
    linarith [Real.sqrt_nonneg ((4*C-Y)*X*Y*(72*C-X))]
  · have hj : 0 < j := by nlinarith
    have hbp : 0 < 6*C*j-X*Y := by linarith
    let s := (6*C*j-X*Y)/((4*C-Y)*j)
    have hs0 : 0 ≤ s := (div_pos hbp (mul_pos hD hj)).le
    have hs3 : s ≤ 3 := by
      apply (div_le_iff₀ (mul_pos hD hj)).mpr
      have hh : 0 ≤ (6*C-3*Y)*j := mul_nonneg (by linarith) hj.le
      nlinarith [hh]
    have hp := mul_le_mul_of_nonneg_left (hq s hs0 hs3) hD.le
    have hid : (4*C-Y)*((s^2*Y+4*C*s*(3-s))*j^2 -
        2*s*X*Y*j-X*Y*(72*C-X)) =
      (6*C*j-X*Y)^2-(4*C-Y)*X*Y*(72*C-X) := by
      dsimp [s]
      field_simp [hD.ne', hj.ne']
      ring
    rw [hid] at hp
    have hbroot := Real.abs_le_sqrt (show (6*C*j-X*Y)^2 ≤
      (4*C-Y)*X*Y*(72*C-X) by linarith)
    rw [abs_of_pos hbp] at hbroot
    apply (le_div_iff₀ (by positivity : 0 < 6*C)).mpr
    linarith

theorem actual_creation_same_test_upper_unit {μ : Measure (Space n)}
    (hn : 1 ≤ n) (hμ : admissibleMeasure μ) {f : Space n → ℝ}
    (hf : MemLp f 2 μ) (hunit : (∫ x, (f x)^2 ∂μ) = 1) :
    let X := actualAppellEnergy μ f 3
    let Y := actualAppellEnergy μ f 2
    properThirdPairing μ f ≤
      (X*Y+Real.sqrt ((4*supportC-Y)*X*Y*(72*supportC-X)))/(2*supportC) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hY8 := actualAppellEnergy_two_le_eight_integral hμ hf
  rw [hunit] at hY8
  have hb := creation_same_test_scalar_upper (by norm_num [supportC])
    (actualAppellEnergy_nonneg μ f 3) (actualAppellEnergy_nonneg μ f 2)
    (by simpa using hY8)
    (fun s hs0 hs3 => actual_creation_same_test_quadratic_unit hn hμ hf hunit hs0 hs3)
  dsimp only
  change properThirdPairing μ f / 3 ≤ _ at hb
  norm_num [supportC] at hb ⊢
  nlinarith [hb]

end KLSConstantImprovement.OriginalUpperRecovery6SameTestCovarianceDraft
#print axioms KLSConstantImprovement.OriginalUpperRecovery6SameTestCovarianceDraft.centeredQuadratic_same_test_covariance
#print axioms KLSConstantImprovement.OriginalUpperRecovery6SameTestCovarianceDraft.actual_mixed_same_test_poincare_unit
#print axioms KLSConstantImprovement.OriginalUpperRecovery6SameTestCovarianceDraft.actual_creation_same_test_quadratic_unit
#print axioms KLSConstantImprovement.OriginalUpperRecovery6SameTestCovarianceDraft.creation_same_test_scalar_upper
#print axioms KLSConstantImprovement.OriginalUpperRecovery6SameTestCovarianceDraft.actual_creation_same_test_upper_unit

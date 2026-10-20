import KLSConstantImprovement.ActualSameTestAffineCubicBarrier
import KLSConstantImprovement.AffineSameTestCreationSeed238452Scalar

/-! Fresh original-law affine_same_test creation seed. The scalar criterion has exact
proof data; this source is prepared for the merger's first kernel check. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric Matrix InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration KLSBelow25
open KLSConstantImprovement.ActualSameTestAffineCubicBarrier
open KLSConstantImprovement.ActualSameTestAffineTerminal
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem factorial_affine_same_test_creation_seed238452_criterion {u z q alpha : ℝ}
    (halpha : alpha < 1)
    (hm : q*(alpha*(9*AffineSameTestCreationSeed238452.B/2)*z-(64/(3*(1-alpha))-17)*u) >
      16+2*affineCreationRatio ((36*AffineSameTestCreationSeed238452.B)*z) (8*u)) :
    q*(alpha*(36*AffineSameTestCreationSeed238452.B)/8*z-
      ((32/(9*(1-alpha))-2)*(2:ℝ)^2+((32/(9*(1-alpha))-2)-3)*2+1)*u-
      2*0/Real.sqrt 8*Real.sqrt u) >
      2*(3:ℝ)^2-3+1+
        2*affineCreationRatio ((36*AffineSameTestCreationSeed238452.B)*z) (8*u) := by
  have ha : 1-alpha ≠ 0 := (sub_pos.mpr halpha).ne'
  convert hm using 1 <;> norm_num [AffineSameTestCreationSeed238452.B]
  all_goals field_simp [ha]
  all_goals ring_nf
  all_goals simp

def affineSameTestCreationCenteredCubicSeed238452Scheme : FactorialScheme :=
  FactorialScheme.of_pos AffineSameTestCreationSeed238452.B 1 AffineSameTestCreationSeed238452.B_positive (by norm_num)

def affineSameTestCreationCenteredCubicSeed238452Barrier :
    AffineCreationCenteredCubicInductionBarrier affineSameTestCreationCenteredCubicSeed238452Scheme.coefficientH where
  toScalarVariableBarrierShape := AffineSameTestCreationSeed238452.seedShape
  threshold_lower := fun u hu => by
    have h3 : affineSameTestCreationCenteredCubicSeed238452Scheme.coefficientH 3 =
        36*AffineSameTestCreationSeed238452.B := by
      rw [FactorialScheme.coefficientH_ge_three (by norm_num : 3 ≤ 3)]
      norm_num [affineSameTestCreationCenteredCubicSeed238452Scheme,FactorialScheme.of_pos,AffineSameTestCreationSeed238452.B]
    change 360 ≤ affineSameTestCreationCenteredCubicSeed238452Scheme.coefficientH 3*AffineSameTestCreationSeed238452.seedPhi u
    rw [h3]
    exact AffineSameTestCreationSeed238452.seed_threshold_lower u hu
  alpha_ge_third := fun _ hu => AffineSameTestCreationSeed238452.seedAlpha_ge_third hu
  criterion := fun u hu => by
    have hm := factorial_affine_same_test_creation_seed238452_criterion
      (AffineSameTestCreationSeed238452.seedAlpha_unit hu).2
      (AffineSameTestCreationSeed238452.centered_affine_same_test_seed_margin u hu)
    have h3 : affineSameTestCreationCenteredCubicSeed238452Scheme.coefficientH 3 =
        36*AffineSameTestCreationSeed238452.B := by
      rw [FactorialScheme.coefficientH_ge_three (by norm_num : 3 ≤ 3)]
      norm_num [affineSameTestCreationCenteredCubicSeed238452Scheme,FactorialScheme.of_pos,AffineSameTestCreationSeed238452.B]
    have hd2 : actualLowerConvolution affineSameTestCreationCenteredCubicSeed238452Scheme.coefficientH 2 = 0 := by
      norm_num [actualLowerConvolution]
    simpa only [AffineSameTestCreationSeed238452.seedShape,AffineSameTestCreationSeed238452.seedPhi,h3,
      FactorialScheme.coefficientH_two,hd2] using hm

theorem actual_appell_joint_cubic_seed_affine_same_test_creation238452 {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖ = 1) :
    actualAppellEnergy μ f 3 ≤ (36*AffineSameTestCreationSeed238452.B)*
      AffineSameTestCreationSeed238452.seedPhi (actualAppellEnergy μ f 2/8) := by
  let μ₀ : ProbabilityMeasure (Space n) := ⟨μ,hμ.isProb⟩
  have hprevious : ∀ r : ℕ,1 ≤ r → r ≤ 2 → ∀ (ν : Measure (Space n)),admissibleMeasure ν →
      ∀ g : Space n → ℝ,MemLp g 2 ν → actualAppellEnergy ν g r ≤ affineSameTestCreationCenteredCubicSeed238452Scheme.coefficientH r*(∫ x,(g x)^2 ∂ν) := by
    intro r hr hr2 ν hν g hg
    have : IsProbabilityMeasure ν := hν.isProb
    have hi : 0 ≤ ∫ x,(g x)^2 ∂ν := integral_nonneg fun x => sq_nonneg _
    have he : r = 1 ∨ r = 2 := by omega
    rcases he with rfl | rfl
    · have hb := actualAppellEnergy_one_le_integral hν hg
      rw [FactorialScheme.coefficientH_one]
      have h1 : (1:ℝ) ≤ affineSameTestCreationCenteredCubicSeed238452Scheme.B/
          affineSameTestCreationCenteredCubicSeed238452Scheme.K := by
        norm_num [affineSameTestCreationCenteredCubicSeed238452Scheme,FactorialScheme.of_pos,AffineSameTestCreationSeed238452.B]
      change actualAppellEnergy ν g 1 ≤ (affineSameTestCreationCenteredCubicSeed238452Scheme.B/
        affineSameTestCreationCenteredCubicSeed238452Scheme.K)*_
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) hi]
    · rw [FactorialScheme.coefficientH_two]
      exact actualAppellEnergy_two_le_eight_integral hν hg
  have hb := actual_affine_creation_centered_cubic_unit_bound (μ₀ := μ₀) hμ
    (fun r _ _ => FactorialScheme.coefficientH_positive r)
    hprevious affineSameTestCreationCenteredCubicSeed238452Barrier hμ f hunit
  change actualAppellEnergy μ f 3 ≤ affineSameTestCreationCenteredCubicSeed238452Scheme.coefficientH 3*
    AffineSameTestCreationSeed238452.seedPhi
      (actualAppellEnergy μ f 2/affineSameTestCreationCenteredCubicSeed238452Scheme.coefficientH 2) at hb
  have h3 : affineSameTestCreationCenteredCubicSeed238452Scheme.coefficientH 3 =
      36*AffineSameTestCreationSeed238452.B := by
    rw [FactorialScheme.coefficientH_ge_three (by norm_num : 3 ≤ 3)]
    norm_num
    change AffineSameTestCreationSeed238452.B*36 = 36*AffineSameTestCreationSeed238452.B
    ring
  rwa [h3,FactorialScheme.coefficientH_two] at hb

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.factorial_affine_same_test_creation_seed238452_criterion
#print axioms KLS.DeterministicBridgeNext.affineSameTestCreationCenteredCubicSeed238452Barrier
#print axioms KLS.DeterministicBridgeNext.actual_appell_joint_cubic_seed_affine_same_test_creation238452

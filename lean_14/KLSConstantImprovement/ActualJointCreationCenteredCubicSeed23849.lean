import KLSConstantImprovement.OptimizedJointCreationCubicBarrier
import KLSConstantImprovement.OptimizedJointCreationSeed23849Scalar

/-! Fresh original-law optimized joint-aware seed. The scalar criterion has exact
proof data; this source is prepared for the merger's first kernel check. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric Matrix InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration KLSBelow25
open KLSConstantImprovement.OptimizedJointCreationCubicBarrier
open KLSConstantImprovement.OptimizedJointCreationTerminal
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem factorial_joint_creation_seed23849_criterion {u z q alpha : ℝ}
    (halpha : alpha < 1)
    (hm : q*(alpha*(9*OptimizedJointCreationSeed23849.B/2)*z-(64/(3*(1-alpha))-17)*u) >
      16+2*Real.sqrt (8*u*jointCreationCoefficient ((36*OptimizedJointCreationSeed23849.B)*z))/
        Real.sqrt ((36*OptimizedJointCreationSeed23849.B)*z)) :
    q*(alpha*(36*OptimizedJointCreationSeed23849.B)/8*z-
      ((32/(9*(1-alpha))-2)*(2:ℝ)^2+((32/(9*(1-alpha))-2)-3)*2+1)*u-
      2*0/Real.sqrt 8*Real.sqrt u) >
      2*(3:ℝ)^2-3+1+
        2*Real.sqrt (8*u*jointCreationCoefficient ((36*OptimizedJointCreationSeed23849.B)*z))/
          Real.sqrt ((36*OptimizedJointCreationSeed23849.B)*z) := by
  have ha : 1-alpha ≠ 0 := (sub_pos.mpr halpha).ne'
  convert hm using 1 <;> norm_num [OptimizedJointCreationSeed23849.B]
  all_goals field_simp [ha]
  all_goals ring_nf
  all_goals simp

def jointCreationCenteredCubicSeed23849Scheme : FactorialScheme :=
  FactorialScheme.of_pos OptimizedJointCreationSeed23849.B 1 OptimizedJointCreationSeed23849.B_positive (by norm_num)

def jointCreationCenteredCubicSeed23849Barrier :
    JointCreationCenteredCubicInductionBarrier jointCreationCenteredCubicSeed23849Scheme.coefficientH where
  toScalarVariableBarrierShape := OptimizedJointCreationSeed23849.seedShape
  alpha_ge_third := fun _ hu => OptimizedJointCreationSeed23849.seedAlpha_ge_third hu
  criterion := fun u hu => by
    have hm := factorial_joint_creation_seed23849_criterion
      (OptimizedJointCreationSeed23849.seedAlpha_unit hu).2
      (OptimizedJointCreationSeed23849.centered_joint_seed_margin u hu)
    have h3 : jointCreationCenteredCubicSeed23849Scheme.coefficientH 3 =
        36*OptimizedJointCreationSeed23849.B := by
      rw [FactorialScheme.coefficientH_ge_three (by norm_num : 3 ≤ 3)]
      norm_num [jointCreationCenteredCubicSeed23849Scheme,FactorialScheme.of_pos,OptimizedJointCreationSeed23849.B]
    have hd2 : actualLowerConvolution jointCreationCenteredCubicSeed23849Scheme.coefficientH 2 = 0 := by
      norm_num [actualLowerConvolution]
    simpa only [OptimizedJointCreationSeed23849.seedShape,OptimizedJointCreationSeed23849.seedPhi,h3,
      FactorialScheme.coefficientH_two,hd2] using hm

theorem actual_appell_joint_cubic_seed_joint_creation23849 {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖ = 1) :
    actualAppellEnergy μ f 3 ≤ (36*OptimizedJointCreationSeed23849.B)*
      OptimizedJointCreationSeed23849.seedPhi (actualAppellEnergy μ f 2/8) := by
  let μ₀ : ProbabilityMeasure (Space n) := ⟨μ,hμ.isProb⟩
  have hprevious : ∀ r : ℕ,1 ≤ r → r ≤ 2 → ∀ (ν : Measure (Space n)),admissibleMeasure ν →
      ∀ g : Space n → ℝ,MemLp g 2 ν → actualAppellEnergy ν g r ≤ jointCreationCenteredCubicSeed23849Scheme.coefficientH r*(∫ x,(g x)^2 ∂ν) := by
    intro r hr hr2 ν hν g hg
    have : IsProbabilityMeasure ν := hν.isProb
    have hi : 0 ≤ ∫ x,(g x)^2 ∂ν := integral_nonneg fun x => sq_nonneg _
    have he : r = 1 ∨ r = 2 := by omega
    rcases he with rfl | rfl
    · have hb := actualAppellEnergy_one_le_integral hν hg
      rw [FactorialScheme.coefficientH_one]
      have h1 : (1:ℝ) ≤ jointCreationCenteredCubicSeed23849Scheme.B/
          jointCreationCenteredCubicSeed23849Scheme.K := by
        norm_num [jointCreationCenteredCubicSeed23849Scheme,FactorialScheme.of_pos,OptimizedJointCreationSeed23849.B]
      change actualAppellEnergy ν g 1 ≤ (jointCreationCenteredCubicSeed23849Scheme.B/
        jointCreationCenteredCubicSeed23849Scheme.K)*_
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) hi]
    · rw [FactorialScheme.coefficientH_two]
      exact actualAppellEnergy_two_le_eight_integral hν hg
  have hb := actual_joint_creation_centered_cubic_unit_bound (μ₀ := μ₀) hμ
    (fun r _ _ => FactorialScheme.coefficientH_positive r)
    hprevious jointCreationCenteredCubicSeed23849Barrier hμ f hunit
  change actualAppellEnergy μ f 3 ≤ jointCreationCenteredCubicSeed23849Scheme.coefficientH 3*
    OptimizedJointCreationSeed23849.seedPhi
      (actualAppellEnergy μ f 2/jointCreationCenteredCubicSeed23849Scheme.coefficientH 2) at hb
  have h3 : jointCreationCenteredCubicSeed23849Scheme.coefficientH 3 =
      36*OptimizedJointCreationSeed23849.B := by
    rw [FactorialScheme.coefficientH_ge_three (by norm_num : 3 ≤ 3)]
    norm_num
    change OptimizedJointCreationSeed23849.B*36 = 36*OptimizedJointCreationSeed23849.B
    ring
  rwa [h3,FactorialScheme.coefficientH_two] at hb

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.factorial_joint_creation_seed23849_criterion
#print axioms KLS.DeterministicBridgeNext.jointCreationCenteredCubicSeed23849Barrier
#print axioms KLS.DeterministicBridgeNext.actual_appell_joint_cubic_seed_joint_creation23849

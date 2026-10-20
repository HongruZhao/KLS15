import ActualCreationCenteredCubicSeed24
import CreationSeed239Scalar
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric Matrix InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration KLSBelow25
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
 theorem factorial_creation_seed239_criterion {u z q alpha : ℝ}
    (_hu : 0≤u) (hz : 0<z) (halpha : alpha<1)
    (hm : q*(alpha*(9*CreationSeed239.B/2)*z-(64/(3*(1-alpha))-17)*u)>
      16+CreationSeed239.seedR*Real.sqrt u/Real.sqrt z) :
    q*(alpha*(36*CreationSeed239.B)/8*z-
      ((32/(9*(1-alpha))-2)*(2:ℝ)^2+((32/(9*(1-alpha))-2)-3)*2+1)*u-
      2*0/Real.sqrt 8*Real.sqrt u) >
      2*(3:ℝ)^2-3+1+2*Real.sqrt (48*8*u)/Real.sqrt ((36*CreationSeed239.B)*z) := by
  have hB : 0 < (36*CreationSeed239.B) := by positivity [CreationSeed239.B_positive]
  have hsz : 0 < Real.sqrt z := Real.sqrt_pos.mpr hz
  have hsB : 0 < Real.sqrt (36*CreationSeed239.B) := Real.sqrt_pos.mpr hB
  have hmajor : (1536:ℝ) ≤ CreationSeed239.seedR^2*(36*CreationSeed239.B) := by
    norm_num [CreationSeed239.seedR,CreationSeed239.B]
  have hconst : 2*Real.sqrt (384:ℝ)/Real.sqrt (36*CreationSeed239.B) ≤ CreationSeed239.seedR := by
    apply (div_le_iff₀ hsB).mpr
    have hR := CreationSeed239.seedR_positive
    have hs384 := Real.sq_sqrt (by norm_num : (0:ℝ)≤384)
    have hsB2 := Real.sq_sqrt hB.le
    have hp : 0≤CreationSeed239.seedR*Real.sqrt (36*CreationSeed239.B) := by positivity
    nlinarith [sq_nonneg (2*Real.sqrt (384:ℝ)+CreationSeed239.seedR*Real.sqrt (36*CreationSeed239.B))]
  have hroot : 2*Real.sqrt (48*8*u)/Real.sqrt ((36*CreationSeed239.B)*z) ≤
      CreationSeed239.seedR*Real.sqrt u/Real.sqrt z := by
    rw [show (48:ℝ)*8*u=384*u by ring, Real.sqrt_mul (by norm_num : (0:ℝ)≤384),
      Real.sqrt_mul hB.le]
    have h := mul_le_mul_of_nonneg_right hconst (div_nonneg (Real.sqrt_nonneg u) hsz.le)
    convert h using 1 <;> field_simp [hsB.ne',hsz.ne']
  have hm' : q*(alpha*(9*CreationSeed239.B/2)*z-(64/(3*(1-alpha))-17)*u)>
      16+2*Real.sqrt (48*8*u)/Real.sqrt ((36*CreationSeed239.B)*z) := by linarith
  have ha : 1-alpha≠0 := (sub_pos.mpr halpha).ne'
  convert hm' using 1 <;> norm_num [CreationSeed239.B]
  all_goals field_simp [ha]
  all_goals ring_nf
  all_goals simp


def creationCenteredCubicSeed239Scheme : FactorialScheme :=
  FactorialScheme.of_pos CreationSeed239.B 1 CreationSeed239.B_positive (by norm_num)

def creationCenteredCubicSeed239Barrier :
    CreationCenteredCubicInductionBarrier creationCenteredCubicSeed239Scheme.coefficientH where
  toScalarVariableBarrierShape := CreationSeed239.seedShape
  alpha_ge_third := fun _ hu => CreationSeed239.seedAlpha_ge_third hu
  criterion := fun u hu => by
    have hm := factorial_creation_seed239_criterion hu.1
      (CreationSeed239.seedInverseBarrier.phi_positive hu)
      (CreationSeed239.seedAlpha_unit hu).2 (CreationSeed239.centered_seed_margin u hu)
    have h3 : creationCenteredCubicSeed239Scheme.coefficientH 3=36*CreationSeed239.B := by
      rw [FactorialScheme.coefficientH_ge_three (by norm_num : 3≤3)]
      norm_num [creationCenteredCubicSeed239Scheme,FactorialScheme.of_pos,CreationSeed239.B]
    have hd2 : actualLowerConvolution creationCenteredCubicSeed239Scheme.coefficientH 2=0 := by
      norm_num [actualLowerConvolution]
    simpa only [CreationSeed239.seedShape,CreationSeed239.seedPhi,h3,FactorialScheme.coefficientH_two,hd2] using hm


 theorem actual_appell_joint_cubic_seed_creation239 {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) :
    actualAppellEnergy μ f 3≤(36*CreationSeed239.B)*
      CreationSeed239.seedPhi (actualAppellEnergy μ f 2/8) := by
  let μ₀ : ProbabilityMeasure (Space n) := ⟨μ,hμ.isProb⟩
  have hprevious : ∀ r : ℕ,1≤r → r≤2 → ∀ (ν : Measure (Space n)),admissibleMeasure ν →
      ∀ g : Space n → ℝ,MemLp g 2 ν → actualAppellEnergy ν g r≤
        creationCenteredCubicSeed239Scheme.coefficientH r*(∫ x,(g x)^2 ∂ν) := by
    intro r hr hr2 ν hν g hg
    have : IsProbabilityMeasure ν := hν.isProb
    have hi : 0≤∫ x,(g x)^2 ∂ν := integral_nonneg fun x => sq_nonneg _
    have he : r=1 ∨ r=2 := by omega
    rcases he with rfl | rfl
    · have hb := actualAppellEnergy_one_le_integral hν hg
      rw [FactorialScheme.coefficientH_one]
      have h1 : (1:ℝ)≤ creationCenteredCubicSeed239Scheme.B/creationCenteredCubicSeed239Scheme.K := by
        norm_num [creationCenteredCubicSeed239Scheme,FactorialScheme.of_pos,CreationSeed239.B]
      change actualAppellEnergy ν g 1≤(creationCenteredCubicSeed239Scheme.B/creationCenteredCubicSeed239Scheme.K)*_
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) hi]
    · rw [FactorialScheme.coefficientH_two]
      exact actualAppellEnergy_two_le_eight_integral hν hg
  have hb := actual_creation_centered_cubic_joint_unit_bound (μ₀:=μ₀) hμ
    (fun r _ _ => FactorialScheme.coefficientH_positive r)
    hprevious creationCenteredCubicSeed239Barrier hμ f hunit
  change actualAppellEnergy μ f 3≤ creationCenteredCubicSeed239Scheme.coefficientH 3*
    CreationSeed239.seedPhi (actualAppellEnergy μ f 2/creationCenteredCubicSeed239Scheme.coefficientH 2) at hb
  have h3 : creationCenteredCubicSeed239Scheme.coefficientH 3=36*CreationSeed239.B := by
    rw [FactorialScheme.coefficientH_ge_three (by norm_num : 3≤3)]
    norm_num
    change CreationSeed239.B*36=36*CreationSeed239.B
    ring
  rwa [h3,FactorialScheme.coefficientH_two] at hb

end KLS.DeterministicBridgeNext

#print axioms KLS.DeterministicBridgeNext.actual_appell_joint_cubic_seed_creation239

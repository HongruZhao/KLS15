import ActualCenteredVariableCoefficientJointSeed
import ActualCreationCenteredAdjacentTerminal
import CreationSeed24Scalar
import ActualAppellCoefficientInduction
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric Matrix InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration KLSBelow25
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

structure CreationCenteredCubicInductionBarrier (h : ℕ → ℝ) extends ScalarVariableBarrierShape where
  alpha_ge_third : ∀ u∈Icc (0:ℝ) 1,(1/3:ℝ)≤alpha u
  criterion : ∀ u∈Icc (0:ℝ) 1,
    (-deriv phi u/phi u)*(alpha u*h 3/h 2*phi u-
      ((32/(9*(1-alpha u))-2)*(2:ℝ)^2+((32/(9*(1-alpha u))-2)-3)*2+1)*u-
      2*actualLowerConvolution h 2/Real.sqrt (h 2)*Real.sqrt u) >
      2*(3:ℝ)^2-3+1+2*Real.sqrt (48*h 2*u)/Real.sqrt (h 3*phi u)

theorem CreationCenteredCubicInductionBarrier.q_positive {h:ℕ→ℝ}
    (b:CreationCenteredCubicInductionBarrier h) {u:ℝ} (hu:u∈Icc (0:ℝ) 1) :
    0 < -deriv b.phi u/b.phi u :=
  div_pos (neg_pos.mpr (b.derivative_negative u hu)) (b.positive u hu)

 theorem actual_creation_centered_cubic_joint_unit_bound {n : ℕ}
    {μ₀ : ProbabilityMeasure (Space n)} (hμ₀ : admissibleMeasure (μ₀ : Measure (Space n)))
    {h : ℕ → ℝ}
    (hh : ∀ r : ℕ, 1 ≤ r → r ≤ 2+1 → 0 < h r)
    (hprevious : ∀ r : ℕ, 1 ≤ r → r ≤ 2 → ∀ (μ : Measure (Space n)), admissibleMeasure μ →
      ∀ f : Space n → ℝ, MemLp f 2 μ → actualAppellEnergy μ f r ≤ h r*(∫ x, (f x)^2 ∂μ))
    (b : CreationCenteredCubicInductionBarrier h)
    {ν : Measure (Space n)} [IsProbabilityMeasure ν] (hν : admissibleMeasure ν)
    (g : Lp ℝ 2 ν) (hg : ‖g‖=1) :
    actualAppellEnergy ν g (2+1) ≤ h (2+1)*b.phi (actualAppellEnergy ν g 2/h 2) := by
  have hhk := hh 2 (by omega) (by omega)
  have hhj := hh (2+1) (by omega) le_rfl
  have hprevk := hprevious 2 (by omega) le_rfl
  obtain ⟨μ,hμ,c,hunit,hmax,hstat,henergy⟩ := exists_actual_joint_maximizer_energy_inequality
    hμ₀ hhk b.continuous b.positive b.antitone b.concave b.hasDeriv hprevk
  let p := boundedDegreePolynomial c
  let f : Lp ℝ 2 (μ : Measure (Space n)) := polynomialLp hμ.logConcave p
  have hpoly : (f : Space n → ℝ) =ᵐ[(μ : Measure (Space n))] polynomialEval p :=
    polynomialLp_coe hμ.logConcave p
  have hfunit : ‖f‖=1 := hunit
  have hfne : f ≠ 0 := by
    intro hfz
    rw [hfz,norm_zero] at hfunit
    norm_num at hfunit
  let X := actualAppellEnergy (μ : Measure (Space n)) f (2+1)
  let Y := actualAppellEnergy (μ : Measure (Space n)) f 2
  let u := Y/(h 2)
  let q := -deriv b.phi u/b.phi u
  have hu : u ∈ Icc (0 : ℝ) 1 := by
    have hu' := actualAppell_ratio_mem_Icc hμ hhk hprevk f hfne
    rw [hfunit,one_pow,mul_one,← actualAppellEnergy_eq_norm_sq] at hu'
    exact hu'
  have hq : 0 < q := b.q_positive hu
  have hstat' : ∀ ell : Lp ℝ 2 (μ : Measure (Space n)),
      inner ℝ (fullClassAppellTensor (2+1) f) (fullClassAppellTensor (2+1) ell)+
      X*q/(h 2)*inner ℝ (fullClassAppellTensor 2 f) (fullClassAppellTensor 2 ell) =
      X*(1+u*q)*inner ℝ f ell := by
    intro ell
    have hs := hstat ell
    simp only [← actualAppellEnergy_eq_norm_sq] at hs
    exact hs
  have hbound : X ≤ h (2+1)*b.phi u := by
    by_contra hn
    have hex : h (2+1)*b.phi u < X := lt_of_not_ge hn
    have hXp : 0<X := (mul_pos hhj (b.positive u hu)).trans hex
    have hmaximum := actual_adjacent_quotient_centered_heat_nonpos hμ (by omega) p hhk hfunit
      b.concave b.positive hprevk (b.hasDeriv u hu) hXp hq.le hmax
    have ht := actualAppell_centered_weighted_energy_inequality_two_creation hμ f hfunit hhk
      (fun r hr hrk => (hh r hr (by omega)).le)
      (fun r hr hrk => hprevious r hr hrk (μ : Measure (Space n)) hμ)
      (b.alpha_ge_third u hu) (b.alpha_unit u hu).2 hq.le hstat' hmaximum
    have hY : Y = h 2*u := by dsimp [u]; field_simp [hhk.ne']
    have hcrit := b.criterion u hu
    exact centered_weighted_terminal_excess_contradiction hhk hhj (b.positive u hu)
      (b.alpha_unit u hu).1 hq (Real.sqrt_nonneg (48*Y)) hex hY (by simpa only [hY,mul_assoc] using hcrit)
      (by
        have ha : 1-b.alpha u≠0 := (sub_pos.mpr (b.alpha_unit u hu).2).ne'
        have ht' : (X*q/h 2)*b.alpha u*X-15*X-
            (X*q/h 2)*(64/(3*(1-b.alpha u))-18)*Y-
            X*(1+u*q)-2*Real.sqrt X*Real.sqrt (48*Y)-
            2*(X*q/h 2)*Real.sqrt Y*actualLowerConvolution h 2≤0 := ht
        convert ht' using 1
        norm_num only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
        field_simp [ha,hhk.ne']
        ring)
  have hmaxbound : coefficientQuotient (fullClassAppellLinearMap hμ.logConcave 2)
      (fullClassAppellLinearMap hμ.logConcave (2+1)) (h 2) b.phi f ≤ h (2+1) := by
    change ‖fullClassAppellTensor (2+1) f‖^2/
      (‖f‖^2*b.phi (‖fullClassAppellTensor 2 f‖^2/(h 2*‖f‖^2))) ≤ _
    rw [hfunit,one_pow,one_mul,mul_one,← actualAppellEnergy_eq_norm_sq,
      ← actualAppellEnergy_eq_norm_sq]
    exact (div_le_iff₀ (b.positive u hu)).mpr hbound
  have hgne : g≠0 := by
    intro he
    rw [he,norm_zero] at hg
    norm_num at hg
  have hug : actualAppellEnergy ν g 2/h 2∈Icc (0:ℝ) 1 := by
    have hhg := actualAppell_ratio_mem_Icc hν hhk hprevk g hgne
    rw [hg,one_pow,mul_one,←actualAppellEnergy_eq_norm_sq] at hhg
    exact hhg
  let ν₀ : ProbabilityMeasure (Space n) := ⟨ν,hν.isProb⟩
  have hgquot := (hmax ν₀ hν g).trans hmaxbound
  change ‖fullClassAppellTensor (2+1) g‖^2/
    (‖g‖^2*b.phi (‖fullClassAppellTensor 2 g‖^2/(h 2*‖g‖^2)))≤h (2+1) at hgquot
  rw [hg,one_pow,one_mul,mul_one,←actualAppellEnergy_eq_norm_sq,
    ←actualAppellEnergy_eq_norm_sq] at hgquot
  exact (div_le_iff₀ (b.positive _ hug)).mp hgquot

 theorem factorial_creation_seed24_criterion {u z q alpha : ℝ}
    (_hu : 0≤u) (hz : 0<z) (halpha : alpha<1)
    (hm : q*(alpha*(9*CreationSeed24.B/2)*z-(64/(3*(1-alpha))-17)*u)>
      16+CreationSeed24.seedR*Real.sqrt u/Real.sqrt z) :
    q*(alpha*(864:ℝ)/8*z-
      ((32/(9*(1-alpha))-2)*(2:ℝ)^2+((32/(9*(1-alpha))-2)-3)*2+1)*u-
      2*0/Real.sqrt 8*Real.sqrt u) >
      2*(3:ℝ)^2-3+1+2*Real.sqrt (48*8*u)/Real.sqrt (864*z) := by
  have hs6 : Real.sqrt (6:ℝ)≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hsz : Real.sqrt z≠0 := (Real.sqrt_pos.mpr hz).ne'
  have hroot : 2*Real.sqrt (48*8*u)/Real.sqrt (864*z)=
      (4/3:ℝ)*Real.sqrt u/Real.sqrt z := by
    rw [show (48:ℝ)*8*u=64*(6*u) by ring,
      show (864:ℝ)*z=144*(6*z) by ring,
      Real.sqrt_mul (by norm_num : (0:ℝ)≤64),
      Real.sqrt_mul (by norm_num : (0:ℝ)≤144),
      Real.sqrt_mul (by norm_num : (0:ℝ)≤6),
      Real.sqrt_mul (by norm_num : (0:ℝ)≤6)]
    norm_num
    field_simp [hs6,hsz]
    ring
  rw [hroot]
  have ha : 1-alpha≠0 := (sub_pos.mpr halpha).ne'
  convert hm using 1 <;> norm_num [CreationSeed24.B,CreationSeed24.seedR]
  all_goals field_simp [ha]
  all_goals ring_nf
  all_goals simp


def creationCenteredCubicSeed24Scheme : FactorialScheme :=
  FactorialScheme.of_pos CreationSeed24.B 1 CreationSeed24.B_positive (by norm_num)

def creationCenteredCubicSeed24Barrier :
    CreationCenteredCubicInductionBarrier creationCenteredCubicSeed24Scheme.coefficientH where
  toScalarVariableBarrierShape := CreationSeed24.seedShape
  alpha_ge_third := fun _ hu => CreationSeed24.seedAlpha_ge_third hu
  criterion := fun u hu => by
    have hm := factorial_creation_seed24_criterion hu.1
      (CreationSeed24.seedInverseBarrier.phi_positive hu)
      (CreationSeed24.seedAlpha_unit hu).2 (CreationSeed24.centered_seed_margin u hu)
    have h3 : creationCenteredCubicSeed24Scheme.coefficientH 3=864 := by
      rw [FactorialScheme.coefficientH_ge_three (by norm_num : 3≤3)]
      norm_num [creationCenteredCubicSeed24Scheme,FactorialScheme.of_pos,CreationSeed24.B]
    have hd2 : actualLowerConvolution creationCenteredCubicSeed24Scheme.coefficientH 2=0 := by
      norm_num [actualLowerConvolution]
    simpa only [CreationSeed24.seedShape,CreationSeed24.seedPhi,h3,FactorialScheme.coefficientH_two,hd2] using hm


 theorem actual_appell_joint_cubic_seed_creation24 {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) :
    actualAppellEnergy μ f 3≤(36*CreationSeed24.B)*
      CreationSeed24.seedPhi (actualAppellEnergy μ f 2/8) := by
  let μ₀ : ProbabilityMeasure (Space n) := ⟨μ,hμ.isProb⟩
  have hprevious : ∀ r : ℕ,1≤r → r≤2 → ∀ (ν : Measure (Space n)),admissibleMeasure ν →
      ∀ g : Space n → ℝ,MemLp g 2 ν → actualAppellEnergy ν g r≤
        creationCenteredCubicSeed24Scheme.coefficientH r*(∫ x,(g x)^2 ∂ν) := by
    intro r hr hr2 ν hν g hg
    have : IsProbabilityMeasure ν := hν.isProb
    have hi : 0≤∫ x,(g x)^2 ∂ν := integral_nonneg fun x => sq_nonneg _
    have he : r=1 ∨ r=2 := by omega
    rcases he with rfl | rfl
    · have hb := actualAppellEnergy_one_le_integral hν hg
      rw [FactorialScheme.coefficientH_one]
      have h1 : (1:ℝ)≤ creationCenteredCubicSeed24Scheme.B/creationCenteredCubicSeed24Scheme.K := by
        norm_num [creationCenteredCubicSeed24Scheme,FactorialScheme.of_pos,CreationSeed24.B]
      change actualAppellEnergy ν g 1≤(creationCenteredCubicSeed24Scheme.B/creationCenteredCubicSeed24Scheme.K)*_
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) hi]
    · rw [FactorialScheme.coefficientH_two]
      exact actualAppellEnergy_two_le_eight_integral hν hg
  have hb := actual_creation_centered_cubic_joint_unit_bound (μ₀:=μ₀) hμ
    (fun r _ _ => FactorialScheme.coefficientH_positive r)
    hprevious creationCenteredCubicSeed24Barrier hμ f hunit
  change actualAppellEnergy μ f 3≤ creationCenteredCubicSeed24Scheme.coefficientH 3*
    CreationSeed24.seedPhi (actualAppellEnergy μ f 2/creationCenteredCubicSeed24Scheme.coefficientH 2) at hb
  have h3 : creationCenteredCubicSeed24Scheme.coefficientH 3=36*CreationSeed24.B := by
    rw [FactorialScheme.coefficientH_ge_three (by norm_num : 3≤3)]
    norm_num
    change CreationSeed24.B*36=36*CreationSeed24.B
    ring
  rwa [h3,FactorialScheme.coefficientH_two] at hb

end KLS.DeterministicBridgeNext

#print axioms KLS.DeterministicBridgeNext.actual_creation_centered_cubic_joint_unit_bound
#print axioms KLS.DeterministicBridgeNext.actual_appell_joint_cubic_seed_creation24

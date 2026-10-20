import ActualSymmetricCenteredCubicSeed245
import ActualCubicGramTerminal

/-! Replay the existing all-law cubic seed using the retained actual cubic Gram.
The maximization, scalar barrier, and analytic hypotheses are unchanged.
The old convolution estimate is not invoked in this proof: sqrt(Gram) is used
first and is only weakened to the old scalar budget when applying its barrier.
This preserves the established endpoint while exposing a sharper budget to
future barriers. It does not assert a universal coefficient-four theorem.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric Matrix InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration KLSBelow25
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
 theorem actual_symmetric_centered_cubic_joint_unit_bound_via_gram {n : ℕ}
    {μ₀ : ProbabilityMeasure (Space n)} (hμ₀ : admissibleMeasure (μ₀ : Measure (Space n)))
    {h : ℕ → ℝ}
    (hh : ∀ r : ℕ, 1 ≤ r → r ≤ 2+1 → 0 < h r)
    (hprevious : ∀ r : ℕ, 1 ≤ r → r ≤ 2 → ∀ (μ : Measure (Space n)), admissibleMeasure μ →
      ∀ f : Space n → ℝ, MemLp f 2 μ → actualAppellEnergy μ f r ≤ h r*(∫ x, (f x)^2 ∂μ))
    (b : SymmetricCenteredCubicInductionBarrier h) (hh2 : h 2 = 8)
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
    have htGram := actualAppell_centered_weighted_energy_inequality_two_gram hμ f hfunit hhk
      (b.alpha_ge_third u hu) (b.alpha_unit u hu).2 hq.le hstat' hmaximum
    have hY8 : Y ≤ 8 := by
      have hy := (div_le_one hhk).mp hu.2
      simpa only [hh2] using hy
    have hGramCap : actualCubicRemainderGram (μ : Measure (Space n)) f ≤ (24 : ℝ)^2 := by
      have hg := actualCubicRemainderGram_le hμ (Lp.memLp f)
      change actualCubicRemainderGram (μ : Measure (Space n)) f ≤ 48*Y at hg
      nlinarith
    have hSqrtGram : Real.sqrt (actualCubicRemainderGram (μ : Measure (Space n)) f) ≤ 24 := by
      have hs := Real.sq_sqrt (actualCubicRemainderGram_nonneg hμ (Lp.memLp f))
      have hn := Real.sqrt_nonneg (actualCubicRemainderGram (μ : Measure (Space n)) f)
      nlinarith
    have hd2 : actualLowerConvolution h 2 = 0 := by norm_num [actualLowerConvolution]
    have hd3 : actualLowerConvolution h 3 = 24 := by norm_num [actualLowerConvolution, hh2]
    have hcost := mul_le_mul_of_nonneg_left hSqrtGram
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg X))
    have ht :
        (X*q/h 2)*b.alpha u*X-15*X-
          (X*q/h 2)*(64/(3*(1-b.alpha u))-18)*Y-
          X*(1+u*q)-2*Real.sqrt X*actualLowerConvolution h 3-
          2*(X*q/h 2)*Real.sqrt Y*actualLowerConvolution h 2 ≤ 0 := by
      rw [hd2, hd3]
      dsimp only at htGram
      change (X*q/h 2)*b.alpha u*X-15*X-
          (X*q/h 2)*(64/(3*(1-b.alpha u))-18)*Y-
          X*(1+u*q)-2*Real.sqrt X*
            Real.sqrt (actualCubicRemainderGram (μ : Measure (Space n)) f) ≤ 0 at htGram
      nlinarith
    have hY : Y = h 2*u := by dsimp [u]; field_simp [hhk.ne']
    have hcrit := b.criterion u hu
    exact centered_weighted_terminal_excess_contradiction hhk hhj (b.positive u hu)
      (b.alpha_unit u hu).1 hq (actualLowerConvolution_nonneg h (2+1)) hex hY hcrit
      (by
        have ha : 1-b.alpha u≠0 := (sub_pos.mpr (b.alpha_unit u hu).2).ne'
        have ht' : (X*q/h 2)*b.alpha u*X-15*X-
            (X*q/h 2)*(64/(3*(1-b.alpha u))-18)*Y-
            X*(1+u*q)-2*Real.sqrt X*actualLowerConvolution h 3-
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

 theorem actual_appell_joint_cubic_seed_245_via_gram {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) :
    actualAppellEnergy μ f 3≤(36*SymmetricCenteredSeed245.B)*
      SymmetricCenteredSeed245.seedPhi (actualAppellEnergy μ f 2/8) := by
  let μ₀ : ProbabilityMeasure (Space n) := ⟨μ,hμ.isProb⟩
  have hprevious : ∀ r : ℕ,1≤r → r≤2 → ∀ (ν : Measure (Space n)),admissibleMeasure ν →
      ∀ g : Space n → ℝ,MemLp g 2 ν → actualAppellEnergy ν g r≤
        symmetricCenteredCubicSeed245Scheme.coefficientH r*(∫ x,(g x)^2 ∂ν) := by
    intro r hr hr2 ν hν g hg
    have : IsProbabilityMeasure ν := hν.isProb
    have hi : 0≤∫ x,(g x)^2 ∂ν := integral_nonneg fun x => sq_nonneg _
    have he : r=1 ∨ r=2 := by omega
    rcases he with rfl | rfl
    · have hb := actualAppellEnergy_one_le_integral hν hg
      rw [FactorialScheme.coefficientH_one]
      have h1 : (1:ℝ)≤ symmetricCenteredCubicSeed245Scheme.B/symmetricCenteredCubicSeed245Scheme.K := by
        norm_num [symmetricCenteredCubicSeed245Scheme,FactorialScheme.of_pos,SymmetricCenteredSeed245.B]
      change actualAppellEnergy ν g 1≤(symmetricCenteredCubicSeed245Scheme.B/symmetricCenteredCubicSeed245Scheme.K)*_
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) hi]
    · rw [FactorialScheme.coefficientH_two]
      exact actualAppellEnergy_two_le_eight_integral hν hg
  have hb := actual_symmetric_centered_cubic_joint_unit_bound_via_gram (μ₀:=μ₀) hμ
    (fun r _ _ => FactorialScheme.coefficientH_positive r)
    hprevious symmetricCenteredCubicSeed245Barrier (by rw [FactorialScheme.coefficientH_two]) hμ f hunit
  change actualAppellEnergy μ f 3≤ symmetricCenteredCubicSeed245Scheme.coefficientH 3*
    SymmetricCenteredSeed245.seedPhi (actualAppellEnergy μ f 2/symmetricCenteredCubicSeed245Scheme.coefficientH 2) at hb
  have h3 : symmetricCenteredCubicSeed245Scheme.coefficientH 3=36*SymmetricCenteredSeed245.B := by
    rw [FactorialScheme.coefficientH_ge_three (by norm_num : 3≤3)]
    norm_num
    change SymmetricCenteredSeed245.B*36=36*SymmetricCenteredSeed245.B
    ring
  rwa [h3,FactorialScheme.coefficientH_two] at hb

end KLS.DeterministicBridgeNext

#print axioms KLS.DeterministicBridgeNext.actual_symmetric_centered_cubic_joint_unit_bound_via_gram
#print axioms KLS.DeterministicBridgeNext.actual_appell_joint_cubic_seed_245_via_gram

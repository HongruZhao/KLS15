import ActualCubicGramCap
import SharperCubicBarrierScalar
/-! A smaller universal cubic cap from the retained actual remainder Gram.
The norm20 budget follows from Gram≤48E2≤384<400, and every rational
scalar barrier certificate is proved in Lean. Original sources are unchanged. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric Matrix InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration KLSBelow25
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
structure SharperCubicInductionBarrier (h : ℕ → ℝ) extends ScalarVariableBarrierShape where
  alpha_ge_third : ∀ u∈Icc (0:ℝ) 1, (1/3:ℝ)≤alpha u
  criterion : ∀ u∈Icc (0:ℝ) 1,
    (-deriv phi u/phi u)*(alpha u*h 3/h 2*phi u-
      ((32/(9*(1-alpha u))-2)*(2:ℝ)^2+((32/(9*(1-alpha u))-2)-3)*2+1)*u-
      2*(0:ℝ)/Real.sqrt (h 2)*Real.sqrt u) >
      2*(3:ℝ)^2-3+1+2*(20:ℝ)/Real.sqrt (h 3*phi u)

 theorem actual_symmetric_centered_cubic_joint_unit_bound_sharper_gram {n : ℕ}
    {μ₀ : ProbabilityMeasure (Space n)} (hμ₀ : admissibleMeasure (μ₀ : Measure (Space n)))
    {h : ℕ → ℝ}
    (hh : ∀ r : ℕ, 1 ≤ r → r ≤ 2+1 → 0 < h r)
    (hprevious : ∀ r : ℕ, 1 ≤ r → r ≤ 2 → ∀ (μ : Measure (Space n)), admissibleMeasure μ →
      ∀ f : Space n → ℝ, MemLp f 2 μ → actualAppellEnergy μ f r ≤ h r*(∫ x, (f x)^2 ∂μ))
    (b : SharperCubicInductionBarrier h) (hh2 : h 2 = 8)
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
  have hq : 0 < q := div_pos (neg_pos.mpr (b.derivative_negative u hu)) (b.positive u hu)
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
    have hGramCap : actualCubicRemainderGram (μ : Measure (Space n)) f ≤ (20 : ℝ)^2 := by
      have hg := actualCubicRemainderGram_le hμ (Lp.memLp f)
      change actualCubicRemainderGram (μ : Measure (Space n)) f ≤ 48*Y at hg
      nlinarith
    have hSqrtGram : Real.sqrt (actualCubicRemainderGram (μ : Measure (Space n)) f) ≤ 20 := by
      have hs := Real.sq_sqrt (actualCubicRemainderGram_nonneg hμ (Lp.memLp f))
      have hn := Real.sqrt_nonneg (actualCubicRemainderGram (μ : Measure (Space n)) f)
      nlinarith
    have hcost := mul_le_mul_of_nonneg_left hSqrtGram
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg X))
    have ht :
        (X*q/h 2)*b.alpha u*X-15*X-
          (X*q/h 2)*(64/(3*(1-b.alpha u))-18)*Y-
          X*(1+u*q)-2*Real.sqrt X*(20:ℝ)-
          2*(X*q/h 2)*Real.sqrt Y*(0:ℝ) ≤ 0 := by
      dsimp only at htGram
      change (X*q/h 2)*b.alpha u*X-15*X-
          (X*q/h 2)*(64/(3*(1-b.alpha u))-18)*Y-
          X*(1+u*q)-2*Real.sqrt X*
            Real.sqrt (actualCubicRemainderGram (μ : Measure (Space n)) f) ≤ 0 at htGram
      nlinarith
    have hY : Y = h 2*u := by dsimp [u]; field_simp [hhk.ne']
    have hcrit := b.criterion u hu
    exact centered_weighted_terminal_excess_contradiction hhk hhj (b.positive u hu)
      (b.alpha_unit u hu).1 hq (by norm_num : (0:ℝ)≤20) hex hY hcrit
      (by
        have ha : 1-b.alpha u≠0 := (sub_pos.mpr (b.alpha_unit u hu).2).ne'
        have ht' : (X*q/h 2)*b.alpha u*X-15*X-
            (X*q/h 2)*(64/(3*(1-b.alpha u))-18)*Y-
            X*(1+u*q)-2*Real.sqrt X*(20:ℝ)-
            2*(X*q/h 2)*Real.sqrt Y*(0:ℝ)≤0 := ht
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

theorem factorial_sharper_gram_seed_criterion (s : FactorialScheme) {u z q alpha : ℝ}
    (halpha : alpha<1)
    (hm : q*(alpha*(9*s.B/2)*z-(64/(3*(1-alpha))-17)*u)>
      16+(20/3)/Real.sqrt (s.B*z)) :
    q*(alpha*s.coefficientH 3/s.coefficientH 2*z-
      ((32/(9*(1-alpha))-2)*(2:ℝ)^2+((32/(9*(1-alpha))-2)-3)*2+1)*u-
      2*(0:ℝ)/Real.sqrt (s.coefficientH 2)*Real.sqrt u) >
      2*(3:ℝ)^2-3+1+2*(20:ℝ)/Real.sqrt (s.coefficientH 3*z) := by
  have h3 : s.coefficientH 3=36*s.B := by
    rw [FactorialScheme.coefficientH_ge_three (by norm_num : 3≤3)]
    norm_num
    ring
  have hs : Real.sqrt (s.coefficientH 3*z)=6*Real.sqrt (s.B*z) := by
    rw [h3,show 36*s.B*z=36*(s.B*z) by ring,Real.sqrt_mul (by norm_num : (0:ℝ)≤36)]
    norm_num
  rw [hs,h3,FactorialScheme.coefficientH_two]
  have ha : 1-alpha≠0 := (sub_pos.mpr halpha).ne'
  convert hm using 1 <;> field_simp [ha] <;> ring

def sharperGramCubicScheme : FactorialScheme :=
  FactorialScheme.of_pos KLSImprovement.SharperCubicBarrier.B 1
    KLSImprovement.SharperCubicBarrier.B_positive (by norm_num)

def sharperGramCubicBarrier : SharperCubicInductionBarrier sharperGramCubicScheme.coefficientH where
  toScalarVariableBarrierShape := SymmetricCenteredSeed245.seedShape
  alpha_ge_third := fun _ hu => SymmetricCenteredSeed245.seedAlpha_ge_third hu
  criterion := fun u hu => by
    convert factorial_sharper_gram_seed_criterion sharperGramCubicScheme
      (SymmetricCenteredSeed245.seedAlpha_unit hu).2
      (KLSImprovement.SharperCubicBarrier.centered_seed_margin u hu) using 1 <;>
        norm_num only [SymmetricCenteredSeed245.seedShape]
 theorem actual_appell_joint_cubic_seed_sharper_gram {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) :
    actualAppellEnergy μ f 3≤(36*KLSImprovement.SharperCubicBarrier.B)*
      SymmetricCenteredSeed245.seedPhi (actualAppellEnergy μ f 2/8) := by
  let μ₀ : ProbabilityMeasure (Space n) := ⟨μ,hμ.isProb⟩
  have hprevious : ∀ r : ℕ,1≤r → r≤2 → ∀ (ν : Measure (Space n)),admissibleMeasure ν →
      ∀ g : Space n → ℝ,MemLp g 2 ν → actualAppellEnergy ν g r≤
        sharperGramCubicScheme.coefficientH r*(∫ x,(g x)^2 ∂ν) := by
    intro r hr hr2 ν hν g hg
    have : IsProbabilityMeasure ν := hν.isProb
    have hi : 0≤∫ x,(g x)^2 ∂ν := integral_nonneg fun x => sq_nonneg _
    have he : r=1 ∨ r=2 := by omega
    rcases he with rfl | rfl
    · have hb := actualAppellEnergy_one_le_integral hν hg
      rw [FactorialScheme.coefficientH_one]
      have h1 : (1:ℝ)≤ sharperGramCubicScheme.B/sharperGramCubicScheme.K := by
        norm_num [sharperGramCubicScheme,FactorialScheme.of_pos,KLSImprovement.SharperCubicBarrier.B]
      change actualAppellEnergy ν g 1≤(sharperGramCubicScheme.B/sharperGramCubicScheme.K)*_
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) hi]
    · rw [FactorialScheme.coefficientH_two]
      exact actualAppellEnergy_two_le_eight_integral hν hg
  have hb := actual_symmetric_centered_cubic_joint_unit_bound_sharper_gram (μ₀:=μ₀) hμ
    (fun r _ _ => FactorialScheme.coefficientH_positive r)
    hprevious sharperGramCubicBarrier (by rw [FactorialScheme.coefficientH_two]) hμ f hunit
  change actualAppellEnergy μ f 3≤ sharperGramCubicScheme.coefficientH 3*
    SymmetricCenteredSeed245.seedPhi (actualAppellEnergy μ f 2/sharperGramCubicScheme.coefficientH 2) at hb
  have h3 : sharperGramCubicScheme.coefficientH 3=36*KLSImprovement.SharperCubicBarrier.B := by
    rw [FactorialScheme.coefficientH_ge_three (by norm_num : 3≤3)]
    norm_num
    change KLSImprovement.SharperCubicBarrier.B*36=36*KLSImprovement.SharperCubicBarrier.B
    ring
  rwa [h3,FactorialScheme.coefficientH_two] at hb

theorem actual_appell_energy_three_sharper_gram_le_norm_sq {n:ℕ}
    {μ:Measure (Space n)} [IsProbabilityMeasure μ] (hμ:admissibleMeasure μ)
    (f:Lp ℝ 2 μ) :
    actualAppellEnergy μ f 3 ≤ (36*KLSImprovement.SharperCubicBarrier.B)*‖f‖^2 := by
  by_cases hf:f=0
  · subst f
    rw [actualAppellEnergy_eq_norm_sq]
    change ‖fullClassAppellLinearMap hμ.logConcave 3 0‖^2≤_
    simp
  have hn:0<‖f‖ := norm_pos_iff.mpr hf
  let g:Lp ℝ 2 μ := ‖f‖⁻¹ • f
  have hg:‖g‖=1 := norm_smul_inv_norm hf
  have hb := actual_appell_joint_cubic_seed_sharper_gram hμ g hg
  have he2 := actualAppellEnergy_two_le_eight_norm_sq hμ g
  rw [hg,one_pow,mul_one] at he2
  have hu:actualAppellEnergy μ g 2/8∈Icc (0:ℝ) 1 :=
    ⟨div_nonneg (actualAppellEnergy_nonneg _ _ _) (by norm_num),
      (div_le_one (by norm_num : (0:ℝ)<8)).mpr he2⟩
  have hp := (SymmetricCenteredSeed245.seedPhi_range hu).2
  have hcap:actualAppellEnergy μ g 3≤36*KLSImprovement.SharperCubicBarrier.B := by
    have hpos:0≤36*KLSImprovement.SharperCubicBarrier.B := by
      have := KLSImprovement.SharperCubicBarrier.B_positive
      positivity
    exact hb.trans (mul_le_of_le_one_right hpos hp)
  calc
    actualAppellEnergy μ f 3=‖f‖^2*actualAppellEnergy μ g 3 := by
      dsimp only [g]
      rw [actualAppellEnergy_smul_Lp_via_gram hμ.logConcave]
      field_simp [hn.ne']
    _ ≤ ‖f‖^2*(36*KLSImprovement.SharperCubicBarrier.B) :=
      mul_le_mul_of_nonneg_left hcap (sq_nonneg _)
    _ = (36*KLSImprovement.SharperCubicBarrier.B)*‖f‖^2 := by ring

theorem actual_appell_energy_three_sharper_gram_le_integral {n:ℕ}
    {μ:Measure (Space n)} (hμ:admissibleMeasure μ) {f:Space n→ℝ} (hf:MemLp f 2 μ) :
    actualAppellEnergy μ f 3 ≤ (36*KLSImprovement.SharperCubicBarrier.B)*(∫ x,(f x)^2 ∂μ) := by
  have : IsProbabilityMeasure μ := hμ.isProb
  rw [actualAppellEnergy_eq_toLp_norm_sq hf]
  have hb := actual_appell_energy_three_sharper_gram_le_norm_sq hμ (hf.toLp f)
  rw [actualAppellEnergy_eq_norm_sq] at hb
  calc
    _ ≤ (36*KLSImprovement.SharperCubicBarrier.B)*‖hf.toLp f‖^2 := hb
    _ = _ := by
      rw [actualLp_norm_sq_eq_integral]
      congr 1
      exact integral_congr_ae (hf.coeFn_toLp.fun_comp (fun t:ℝ => t^2))

theorem actual_appell_energy_three_le_2445_norm_sq {n:ℕ}
    {μ:Measure (Space n)} [IsProbabilityMeasure μ] (hμ:admissibleMeasure μ)
    (f:Lp ℝ 2 μ) : actualAppellEnergy μ f 3 ≤ (36*(489/20:ℝ))*‖f‖^2 := by
  simpa only [KLSImprovement.SharperCubicBarrier.B] using
    actual_appell_energy_three_sharper_gram_le_norm_sq hμ f

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_appell_joint_cubic_seed_sharper_gram
#print axioms KLS.DeterministicBridgeNext.actual_appell_energy_three_sharper_gram_le_norm_sq
#print axioms KLS.DeterministicBridgeNext.actual_appell_energy_three_sharper_gram_le_integral
#print axioms KLS.DeterministicBridgeNext.actual_appell_energy_three_le_2445_norm_sq

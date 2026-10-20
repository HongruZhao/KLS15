import KLSConstantImprovement.AllRankResidualWeightedGenerator
import ActualCreationCenteredCubicSeed239

/-! A reusable actual universal weighted-budget theorem.
The certificate contains only scalar inequalities. Every original-law
maximum, drift, creation bound, and previous-budget induction is discharged
internally. A numerical profile must still supply an exact certificate. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ParameterizedWeightedBudget
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.AllRankResidualWeightedGenerator
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

structure Parameters where
  K : ℝ
  C : ℝ
  c : ℝ
  young : ℕ → ℝ
  alpha : ℕ → ℝ
  zeta2 : ℕ → ℝ
  zeta3 : ℕ → ℝ

def cost (P : Parameters) : ℕ → ℝ :=
  cubicExcludedHarmonicCost P.K P.C P.young P.zeta2 P.zeta3

def coefficient (P : Parameters) (d : ℕ) : ℝ :=
  allRankJointCubicTailCoefficient P.K P.alpha (cost P) d

def head (P : Parameters) : ℝ :=
  jointCubicHeadCoefficient P.K (P.young 2) P.alpha (cost P)

def headPolynomial (P : Parameters) (t : ℝ) : ℝ :=
  P.c*P.C-(P.c+head P)*(2/P.K^2)*(t^2*(CreationSeed239.seedV t)^2)-
    (P.c-coefficient P 3)*(CreationSeed239.B/P.K^3)*(1-t^2)

/-- Rational polynomial positivity discharges the inverse-barrier head condition. -/
theorem head_margin_of_polynomial (P : Parameters)
    (hp : ∀ t, t ∈ Icc (0 : ℝ) CreationSeed239.seedT → 0 < headPolynomial P t)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    (P.c+head P)*(2/P.K^2)*u+
      (P.c-coefficient P 3)*(CreationSeed239.B/P.K^3)*CreationSeed239.seedPhi u < P.c*P.C := by
  have hr := CreationSeed239.seedParameter_range hu
  have hh := hp (CreationSeed239.seedParameter u) hr
  unfold headPolynomial at hh
  rw [←CreationSeed239.seedPhi_u_identity hu,←CreationSeed239.seedPhi_z_identity hu] at hh
  linarith

/-- All fields concern explicit real scalars or sequences of real scalars.
There is no law-dependent hypothesis in this certificate. -/
structure ScalarCertificate (P : Parameters) : Prop where
  K_positive : 0 < P.K
  c_positive : 0 < P.c
  base_budget : 2/P.K^2 ≤ P.C
  young_positive : ∀ b, 2 ≤ b → 0 < P.young b
  zeta2_nonneg : ∀ b, 2 ≤ b → 0 ≤ P.zeta2 b
  zeta2_cap : ∀ b, 2 ≤ b → 2*P.zeta2 b < (b : ℝ)*((b : ℝ)+1)
  zeta3_nonneg : ∀ b, 2 ≤ b → 0 ≤ P.zeta3 b
  zeta3_cap : ∀ (b : ℕ), 2 ≤ b → tripleHarmonicRatio (b : ℝ)*P.zeta3 b < 1
  alpha_nonneg : ∀ d, 2 ≤ d → 0 ≤ P.alpha d
  alpha_lt_one : ∀ d, 2 ≤ d → P.alpha d < 1
  alpha_two : (1 : ℝ)/3 ≤ P.alpha 2
  alpha_three : (1 : ℝ)/2 ≤ P.alpha 3
  alpha_low : ∀ d, 4 ≤ d → P.alpha d ≤ ((d : ℝ)-1)/((d : ℝ)+1)
  Q_sign : 2+1/(P.K*P.young 2)-
    4*(1+1/(6*P.K))^2/(3*(1-P.alpha 2)) ≤ 0
  R_sign : 1-8*(1+1/(6*P.K))^2/(3*(1-P.alpha 2)) ≤ 0
  coefficient_lower : ∀ d, 4 ≤ d → P.c ≤ coefficient P d
  head_nonneg : 0 ≤ P.c+head P
  third_nonneg : 0 ≤ P.c-coefficient P 3
  head_margin : ∀ u, u ∈ Icc (0 : ℝ) 1 →
    (P.c+head P)*(2/P.K^2)*u+
      (P.c-coefficient P 3)*(CreationSeed239.B/P.K^3)*CreationSeed239.seedPhi u < P.c*P.C

theorem ScalarCertificate.C_nonneg {P : Parameters} (h : ScalarCertificate P) : 0 ≤ P.C :=
  (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg P.K)).trans h.base_budget

theorem finite_energy_head_reduction (P : Parameters) (h : ScalarCertificate P)
    (e : ℕ → ℝ) (N : ℕ) (hN : 3 ≤ N)
    (he : ∀ d ∈ Finset.Icc 4 N, 0 ≤ e d)
    (hgen : (∑ d ∈ Finset.Icc 3 N, coefficient P d*e d)-head P*e 2 ≤ 0) :
    P.c*(∑ d ∈ Finset.Icc 2 N, e d)-
      (P.c+head P)*e 2-(P.c-coefficient P 3)*e 3 ≤ 0 := by
  classical
  have htail : P.c*(∑ d ∈ Finset.Icc 4 N, e d) ≤
      ∑ d ∈ Finset.Icc 4 N, coefficient P d*e d := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun d hd => mul_le_mul_of_nonneg_right
      (h.coefficient_lower d (Finset.mem_Icc.mp hd).1) (he d hd)
  have hset3 : Finset.Icc 3 N = insert 3 (Finset.Icc 4 N) := by
    ext d
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  have hset2 : Finset.Icc 2 N = insert 2 (Finset.Icc 3 N) := by
    ext d
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  have hn3 : 3 ∉ Finset.Icc 4 N := by simp
  have hn2 : 2 ∉ Finset.Icc 3 N := by simp
  rw [hset3,Finset.sum_insert hn3] at hgen
  rw [hset2,Finset.sum_insert hn2,hset3,Finset.sum_insert hn3]
  nlinarith

theorem finite_energy_sum_lt_budget (P : Parameters) (h : ScalarCertificate P)
    (e : ℕ → ℝ) (N : ℕ) (hN : 3 ≤ N)
    (he : ∀ d ∈ Finset.Icc 4 N, 0 ≤ e d) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (he2 : e 2 ≤ (2/P.K^2)*u)
    (he3 : e 3 ≤ (CreationSeed239.B/P.K^3)*CreationSeed239.seedPhi u)
    (hgen : (∑ d ∈ Finset.Icc 3 N, coefficient P d*e d)-head P*e 2 ≤ 0) :
    (∑ d ∈ Finset.Icc 2 N, e d) < P.C := by
  have hg := finite_energy_head_reduction P h e N hN he hgen
  have h2 := mul_le_mul_of_nonneg_left he2 h.head_nonneg
  have h3 := mul_le_mul_of_nonneg_left he3 h.third_nonneg
  have hm := h.head_margin u hu
  by_contra hn
  have hM := mul_le_mul_of_nonneg_left (le_of_not_gt hn) h.c_positive.le
  nlinarith

theorem actual_weighted_energy_small_degree (P : Parameters) (h : ScalarCertificate P)
    {n N : ℕ} (hN : N ≤ 2) {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    actualWeightedAppellEnergy μ f P.K N ≤ P.C*(∫ x, (f x)^2 ∂μ) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hi : 0 ≤ ∫ x, (f x)^2 ∂μ := integral_nonneg fun x => sq_nonneg _
  by_cases h2 : N = 2
  · subst N
    have hb := actualAppellEnergy_two_le_eight_integral hμ hf
    have hnorm : actualWeightedAppellEnergy μ f P.K 2 =
        (P.K^2*(Nat.factorial 2 : ℝ)^2)⁻¹*actualAppellEnergy μ f 2 := by
      norm_num [actualWeightedAppellEnergy]
    rw [hnorm]
    calc
      _ ≤ (P.K^2*(Nat.factorial 2 : ℝ)^2)⁻¹*(8*(∫ x, (f x)^2 ∂μ)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (2/P.K^2)*(∫ x, (f x)^2 ∂μ) := by
        norm_num
        field_simp
        ring
      _ ≤ P.C*(∫ x, (f x)^2 ∂μ) := mul_le_mul_of_nonneg_right h.base_budget hi
  · have hn : N < 2 := by omega
    have he : Finset.Icc 2 N = ∅ := Finset.Icc_eq_empty_of_lt hn
    simp only [actualWeightedAppellEnergy,he,Finset.sum_empty]
    exact mul_nonneg h.C_nonneg hi

/-- Original admissible laws and all actual L2 tests, in every finite degree.
Only the explicit scalar certificate is supplied by a profile. -/
theorem actual_weighted_energy_le (P : Parameters) (h : ScalarCertificate P) (N : ℕ)
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    actualWeightedAppellEnergy μ f P.K N ≤ P.C*(∫ x, (f x)^2 ∂μ) := by
  have hall : ∀ N : ℕ, ∀ ν : Measure (Space n), admissibleMeasure ν →
      ∀ g : Space n → ℝ, MemLp g 2 ν →
      actualWeightedAppellEnergy ν g P.K N ≤ P.C*(∫ x, (g x)^2 ∂ν) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro ν hν g hg
      let : IsProbabilityMeasure ν := hν.isProb
      by_cases hsmall : N ≤ 2
      · exact actual_weighted_energy_small_degree P h hsmall hν hg
      have hN : 3 ≤ N := by omega
      let ν₀ : ProbabilityMeasure (Space n) := ⟨ν,hν.isProb⟩
      obtain ⟨μ',hμ',q,hunit,hglobal,hstat,hheat⟩ :=
        exists_actual_centered_weighted_maximum_energy_inequality (N := N) (K := P.K)
          (μ₀ := ν₀) h.K_positive hν
      let f₀ := polynomialLp hμ'.logConcave (boundedDegreePolynomial q)
      let M := actualWeightedAppellEnergy (μ' : Measure (Space n)) f₀ P.K N
      have hprevious : ∀ a : Space n → ℝ, MemLp a 2 (μ' : Measure (Space n)) →
          actualWeightedAppellEnergy (μ' : Measure (Space n)) a P.K (N-1) ≤
            P.C*(∫ x, (a x)^2 ∂(μ' : Measure (Space n))) := by
        intro a ha
        exact ih (N-1) (by omega) (μ' : Measure (Space n)) hμ' a ha
      have hgen := actual_all_rank_joint_cubic_harmonic_generator_coefficients_nonpos hμ' f₀
        hunit P.young P.zeta2 P.zeta3 h.K_positive h.young_positive
        h.zeta2_nonneg h.zeta2_cap h.zeta3_nonneg h.zeta3_cap P.alpha
        h.alpha_nonneg h.alpha_lt_one h.alpha_two h.alpha_three h.alpha_low h.Q_sign h.R_sign
        N hN hprevious hstat hheat
      let u := actualAppellEnergy (μ' : Measure (Space n)) f₀ 2/8
      have hu : u ∈ Icc (0 : ℝ) 1 := by
        have hb := actualAppellEnergy_two_le_eight_norm_sq hμ' f₀
        rw [hunit] at hb
        dsimp only [u]
        constructor
        · exact div_nonneg (actualAppellEnergy_nonneg _ _ _) (by norm_num)
        · norm_num at hb ⊢
          linarith
      have he2 : (P.K^2*(Nat.factorial 2 : ℝ)^2)⁻¹*
          actualAppellEnergy (μ' : Measure (Space n)) f₀ 2 ≤ (2/P.K^2)*u := by
        dsimp only [u]
        norm_num <;> field_simp <;> ring_nf <;> exact le_rfl
      have he3 : (P.K^3*(Nat.factorial 3 : ℝ)^2)⁻¹*
          actualAppellEnergy (μ' : Measure (Space n)) f₀ 3 ≤
          (CreationSeed239.B/P.K^3)*CreationSeed239.seedPhi u := by
        have hb := actual_appell_joint_cubic_seed_creation239 hμ' f₀ hunit
        change actualAppellEnergy (μ' : Measure (Space n)) f₀ 3 ≤
          (36*CreationSeed239.B)*CreationSeed239.seedPhi u at hb
        calc
          _ ≤ (P.K^3*(Nat.factorial 3 : ℝ)^2)⁻¹*
              ((36*CreationSeed239.B)*CreationSeed239.seedPhi u) :=
            mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr
              (mul_nonneg (pow_nonneg h.K_positive.le _) (sq_nonneg _)))
          _ = _ := by
            norm_num <;> field_simp <;> ring
      have hM : M < P.C := by
        apply finite_energy_sum_lt_budget P h
          (fun d => (P.K^d*(d.factorial : ℝ)^2)⁻¹*
            actualAppellEnergy (μ' : Measure (Space n)) f₀ d) N hN
        · intro d hd
          exact mul_nonneg (inv_nonneg.mpr
            (mul_nonneg (pow_nonneg h.K_positive.le _) (sq_nonneg _)))
            (actualAppellEnergy_nonneg _ _ _)
        · exact hu
        · exact he2
        · exact he3
        · exact hgen
      have hnorm : ‖hg.toLp g‖^2 = ∫ x, (g x)^2 ∂ν := by
        rw [actualLp_norm_sq_eq_integral]
        exact integral_congr_ae (hg.coeFn_toLp.fun_comp (fun t : ℝ => t^2))
      calc
        actualWeightedAppellEnergy ν g P.K N =
            actualWeightedAppellEnergy ν (hg.toLp g) P.K N :=
          (actualWeightedAppellEnergy_congr_ae hg.coeFn_toLp P.K N).symm
        _ ≤ M*‖hg.toLp g‖^2 := hglobal ν₀ hν (hg.toLp g)
        _ ≤ P.C*‖hg.toLp g‖^2 := mul_le_mul_of_nonneg_right hM.le (sq_nonneg _)
        _ = P.C*(∫ x, (g x)^2 ∂ν) := by rw [hnorm]
  exact hall N μ hμ f hf

theorem actual_weighted_energy_norm_sq_le (P : Parameters) (h : ScalarCertificate P) (N : ℕ)
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) :
    actualWeightedAppellEnergy μ f P.K N ≤ P.C*‖f‖^2 := by
  have hb := actual_weighted_energy_le P h N hμ (Lp.memLp f)
  rwa [←actualLp_norm_sq_eq_integral] at hb

/-- Four exact signs certify a cubic on the complete half-line x >= D. -/
theorem cubic_nonneg_on_tail (q b a z D x : ℝ) (hx : D ≤ x)
    (hq : 0 ≤ q) (hsecond : 0 ≤ 3*q*D+b)
    (hfirst : 0 ≤ 3*q*D^2+2*b*D+a)
    (hvalue : 0 ≤ q*D^3+b*D^2+a*D+z) :
    0 ≤ q*x^3+b*x^2+a*x+z := by
  have ht : 0 ≤ x-D := sub_nonneg.mpr hx
  calc
    0 ≤ (q*D^3+b*D^2+a*D+z)+(3*q*D^2+2*b*D+a)*(x-D)+
        (3*q*D+b)*(x-D)^2+q*(x-D)^3 := by positivity
    _ = _ := by ring

/-- A finite profile and the rational-cleared cubic tail give all coefficients. -/
theorem coefficient_lower_of_finite_and_cubic_tail (P : Parameters) (D : ℕ) (_hD : 4 ≤ D)
    (q b a z : ℝ)
    (hfinite : ∀ d, 4 ≤ d → d < D → P.c ≤ coefficient P d)
    (htail : ∀ d, D ≤ d → ((d : ℝ)-1)*(coefficient P d-P.c) =
      q*(d : ℝ)^3+b*(d : ℝ)^2+a*(d : ℝ)+z)
    (hq : 0 ≤ q) (hsecond : 0 ≤ 3*q*(D : ℝ)+b)
    (hfirst : 0 ≤ 3*q*(D : ℝ)^2+2*b*(D : ℝ)+a)
    (hvalue : 0 ≤ q*(D : ℝ)^3+b*(D : ℝ)^2+a*(D : ℝ)+z) :
    ∀ d, 4 ≤ d → P.c ≤ coefficient P d := by
  intro d hd
  by_cases hsmall : d < D
  · exact hfinite d hd hsmall
  · have hlarge : D ≤ d := by omega
    have hdr : (4 : ℝ) ≤ d := by exact_mod_cast hd
    have hDr : (D : ℝ) ≤ d := by exact_mod_cast hlarge
    have hp := cubic_nonneg_on_tail q b a z D d hDr hq hsecond hfirst hvalue
    rw [←htail d hlarge] at hp
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (by linarith : 0 < (d : ℝ)-1)).mp hp)

end KLSConstantImprovement.ParameterizedWeightedBudget
#print axioms KLSConstantImprovement.ParameterizedWeightedBudget.actual_weighted_energy_le
#print axioms KLSConstantImprovement.ParameterizedWeightedBudget.actual_weighted_energy_norm_sq_le
#print axioms KLSConstantImprovement.ParameterizedWeightedBudget.coefficient_lower_of_finite_and_cubic_tail
#print axioms KLSConstantImprovement.ParameterizedWeightedBudget.head_margin_of_polynomial

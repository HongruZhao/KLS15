import KLSConstantImprovement.RawCubicQuarticWeightedHead

/-! Actual original-law all-rank induction with a same-test quartic head.
The two law inputs are an explicit universal raw cubic bound and an
explicit cubic/quartic support for unit tests. The generic cubic-to-quartic
barrier transfer will discharge the latter from the former.
-/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix
open scoped BigOperators
namespace KLSConstantImprovement.RawCubicQuarticWeightedBudget
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open TriplePositiveEnergyWeightedBudget
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

abbrev UniversalRawCubicBound := RawCubicWeightedBudget.UniversalRawCubicBound

def UniversalCubicQuarticUnitSupport (A B : ℝ) : Prop :=
  ∀ {n : ℕ} {μ : Measure (Space n)}, admissibleMeasure μ →
    ∀ (f : Lp ℝ 2 μ), ‖f‖ = 1 →
      actualAppellEnergy μ f 4 / 576 + A * (actualAppellEnergy μ f 3 / 36) ≤ B

variable {H A B : ℝ}

structure ScalarCertificate (P : Parameters) (H A B : ℝ) : Prop where
  K_positive : 0 < P.K
  c_positive : 0 < P.c
  base_budget : 2*P.t 2/P.K^2 ≤ P.C
  weight_positive : ∀ d, 2 ≤ d → 0 < P.t d
  young_positive : ∀ b, 2 ≤ b → 0 < P.young b
  theta_nonneg : ∀ d, 3 ≤ d → 0 ≤ P.theta d
  theta_le_one : ∀ d, 3 ≤ d → P.theta d ≤ 1
  alpha_nonneg : ∀ d, 2 ≤ d → 0 ≤ P.alpha d
  alpha_lt_one : ∀ d, 2 ≤ d → P.alpha d < 1
  lambda_nonneg : ∀ d, 2 ≤ d → 0 ≤ P.lambda d
  lambda_le_one : ∀ d, 2 ≤ d → P.lambda d ≤ 1
  lambda_boundary : ∀ d, 2 ≤ d → P.lambda d=1 → P.theta (d+1)=1
  zeta_nonneg : ∀ b,2 ≤ b → 0 ≤ P.zeta b
  zeta_cap : ∀ (b : ℕ),2 ≤ b → tripleHarmonicRatio (b : ℝ)*P.zeta b<1
  quadratic_payment : 3+PositiveEnergyWeightedDrift.kappa P.K P.young P.t P.lambda 2 ≤
    4*(PositiveEnergyWeightedGenerator.gamma P.K P.t P.theta 2)^2/(1-P.alpha 2)
  terminal_payment : ∀ (d : ℕ), 3 ≤ d →
    ((d : ℝ)+PositiveEnergyWeightedDrift.kappa P.K P.young P.t P.lambda d)*(1-P.alpha d) ≤ (d : ℝ)
  coefficient_lower : ∀ d, 5 ≤ d → P.c ≤ coefficient P d
  head_nonneg : 0 ≤ P.c+head P
  fourth_nonneg : 0 ≤ RawCubicQuarticWeightedHead.quarticCoefficient P
  small_three_budget : 2 * P.t 2 / P.K ^ 2 + P.t 3 * H / (36 * P.K ^ 3) ≤ P.C
  head_margin : RawCubicQuarticWeightedHead.headBound P H A B < P.c * P.C

theorem ScalarCertificate.C_nonneg {P : Parameters} (h : ScalarCertificate P H A B) : 0 ≤ P.C :=
  (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (h.weight_positive 2 (by omega)).le) (sq_nonneg P.K)).trans h.base_budget

theorem ScalarCertificate.weight_nonneg {P : Parameters} (h : ScalarCertificate P H A B)
    (d : ℕ) (hd : 2 ≤ d) : 0 ≤ weight P d :=
  (PositiveEnergyWeightedDrift.weight_positive h.K_positive P.t d (h.weight_positive d hd)).le

theorem actual_weighted_energy_small_degree (P : Parameters)
    (h : ScalarCertificate P H A B) (hraw : UniversalRawCubicBound H)
    {n N : ℕ} (hN : N ≤ 3) {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    GeneralWeighted.energy μ f (weight P) N ≤ P.C * (∫ x, (f x) ^ 2 ∂μ) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hi : 0 ≤ ∫ x, (f x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hb2 := actualAppellEnergy_two_le_eight_integral hμ hf
  by_cases h3 : N = 3
  · subst N
    have hb3 := hraw hμ hf
    have he : GeneralWeighted.energy μ f (weight P) 3 =
        weight P 2 * actualAppellEnergy μ f 2 + weight P 3 * actualAppellEnergy μ f 3 := by
      rw [GeneralWeighted.energy, show Finset.Icc 2 3 = {2,3} by decide]
      simp
    rw [he]
    calc
      _ ≤ weight P 2 * (8 * (∫ x, (f x) ^ 2 ∂μ)) +
          weight P 3 * (H * (∫ x, (f x) ^ 2 ∂μ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hb2 (h.weight_nonneg 2 (by omega)))
          (mul_le_mul_of_nonneg_left hb3 (h.weight_nonneg 3 (by omega)))
      _ = (2 * P.t 2 / P.K ^ 2 + P.t 3 * H / (36 * P.K ^ 3)) *
          (∫ x, (f x) ^ 2 ∂μ) := by
        norm_num [weight, PositiveEnergyWeightedDrift.weight, CoupledEnergy.factorialWeight]
        field_simp
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h.small_three_budget hi
  · by_cases h2 : N = 2
    · subst N
      have he : GeneralWeighted.energy μ f (weight P) 2 =
          weight P 2 * actualAppellEnergy μ f 2 := by norm_num [GeneralWeighted.energy]
      rw [he]
      calc
        _ ≤ weight P 2 * (8 * (∫ x, (f x) ^ 2 ∂μ)) :=
          mul_le_mul_of_nonneg_left hb2 (h.weight_nonneg 2 (by omega))
        _ = (2 * P.t 2 / P.K ^ 2) * (∫ x, (f x) ^ 2 ∂μ) := by
          norm_num [weight, PositiveEnergyWeightedDrift.weight, CoupledEnergy.factorialWeight]
          field_simp
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h.base_budget hi
    · have hn : N < 2 := by omega
      have he : Finset.Icc 2 N = ∅ := Finset.Icc_eq_empty_of_lt hn
      simp only [GeneralWeighted.energy, he, Finset.sum_empty]
      exact mul_nonneg h.C_nonneg hi

theorem actual_weighted_energy_le (P : Parameters) (h : ScalarCertificate P H A B) (hraw : UniversalRawCubicBound H)
    (hquartic : UniversalCubicQuarticUnitSupport A B) (N : ℕ)
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    GeneralWeighted.energy μ f (weight P) N ≤ P.C*(∫ x, (f x)^2 ∂μ) := by
  have hall : ∀ N : ℕ, ∀ ν : Measure (Space n), admissibleMeasure ν →
      ∀ g : Space n → ℝ, MemLp g 2 ν →
      GeneralWeighted.energy ν g (weight P) N ≤ P.C*(∫ x, (g x)^2 ∂ν) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro ν hν g hg
      let : IsProbabilityMeasure ν := hν.isProb
      by_cases hsmall : N ≤ 3
      · exact actual_weighted_energy_small_degree P h hraw hsmall hν hg
      have hN : 4 ≤ N := by omega
      let ν₀ : ProbabilityMeasure (Space n) := ⟨ν,hν.isProb⟩
      obtain ⟨μ',hμ',q,hunit,hglobal,hstat,hheat⟩ :=
        GeneralWeighted.exists_centered_maximum_energy_inequality (N := N)
          (μ₀ := ν₀) (weight P) (fun d hd => (PositiveEnergyWeightedDrift.weight_positive h.K_positive P.t d (h.weight_positive d hd)).le) hν
      let f₀ := polynomialLp hμ'.logConcave (boundedDegreePolynomial q)
      let M := GeneralWeighted.energy (μ' : Measure (Space n)) f₀ (weight P) N
      have hprevious : ∀ a : Space n → ℝ, MemLp a 2 (μ' : Measure (Space n)) →
          GeneralWeighted.energy (μ' : Measure (Space n)) a (weight P) (N-1) ≤
            P.C*(∫ x, (a x)^2 ∂(μ' : Measure (Space n))) := by
        intro a ha
        exact ih (N-1) (by omega) (μ' : Measure (Space n)) hμ' a ha
      have hgen := TriplePositiveEnergyWeightedGenerator.actual_generator_coefficients_nonpos hμ' f₀
        hunit h.K_positive P.young P.t P.alpha P.theta P.lambda P.zeta h.young_positive h.weight_positive
        h.alpha_nonneg h.alpha_lt_one h.theta_nonneg h.theta_le_one h.lambda_nonneg h.lambda_le_one
        h.lambda_boundary h.zeta_nonneg h.zeta_cap h.quadratic_payment h.terminal_payment N (by omega) hprevious hstat hheat
      have he2 : weight P 2*
          actualAppellEnergy (μ' : Measure (Space n)) f₀ 2 ≤ 2*P.t 2/P.K^2 := by
        have hb := actualAppellEnergy_two_le_eight_norm_sq hμ' f₀
        rw [hunit] at hb
        norm_num at hb
        calc
          _ ≤ weight P 2*8 := mul_le_mul_of_nonneg_left hb (h.weight_nonneg 2 (by omega))
          _ = _ := by
            norm_num [weight,PositiveEnergyWeightedDrift.weight,CoupledEnergy.factorialWeight] <;>
              field_simp <;> ring
      let Y := actualAppellEnergy (μ' : Measure (Space n)) f₀ 3 / 36
      let Z := actualAppellEnergy (μ' : Measure (Space n)) f₀ 4 / 576
      have hy : 0 ≤ Y := div_nonneg (actualAppellEnergy_nonneg _ _ _) (by norm_num)
      have hycap : Y ≤ H / 36 := by
        have hb := hraw hμ' (Lp.memLp f₀)
        rw [← actualLp_norm_sq_eq_integral, hunit] at hb
        norm_num at hb
        exact div_le_div_of_nonneg_right hb (by norm_num)
      have hs : Z + A * Y ≤ B := hquartic hμ' f₀ hunit
      have he3 : weight P 3 * actualAppellEnergy (μ' : Measure (Space n)) f₀ 3 =
          P.t 3 * Y / P.K ^ 3 := by
        norm_num [Y, weight, PositiveEnergyWeightedDrift.weight, CoupledEnergy.factorialWeight]
        field_simp <;> ring
      have he4 : weight P 4 * actualAppellEnergy (μ' : Measure (Space n)) f₀ 4 =
          P.t 4 * Z / P.K ^ 4 := by
        norm_num [Z, weight, PositiveEnergyWeightedDrift.weight, CoupledEnergy.factorialWeight]
        field_simp <;> ring
      have hM : M < P.C := by
        apply RawCubicQuarticWeightedHead.finite_energy_sum_lt_budget P
          h.K_positive h.c_positive h.coefficient_lower h.head_nonneg h.fourth_nonneg h.head_margin
          (fun d => weight P d * actualAppellEnergy (μ' : Measure (Space n)) f₀ d)
          N hN
        · intro d hd
          exact mul_nonneg (h.weight_nonneg d (by have := (Finset.mem_Icc.mp hd).1; omega))
            (actualAppellEnergy_nonneg _ _ _)
        · exact he2
        · exact he3
        · exact he4
        · exact hy
        · exact hycap
        · exact hs
        · exact hgen
      have hnorm : ‖hg.toLp g‖^2 = ∫ x, (g x)^2 ∂ν := by
        rw [actualLp_norm_sq_eq_integral]
        exact integral_congr_ae (hg.coeFn_toLp.fun_comp (fun t : ℝ => t^2))
      calc
        GeneralWeighted.energy ν g (weight P) N =
            GeneralWeighted.energy ν (hg.toLp g) (weight P) N :=
          (GeneralWeighted.energy_congr_ae hg.coeFn_toLp (weight P) N).symm
        _ ≤ M*‖hg.toLp g‖^2 := hglobal ν₀ hν (hg.toLp g)
        _ ≤ P.C*‖hg.toLp g‖^2 := mul_le_mul_of_nonneg_right hM.le (sq_nonneg _)
        _ = P.C*(∫ x, (g x)^2 ∂ν) := by rw [hnorm]
  exact hall N μ hμ f hf

theorem actual_weighted_energy_norm_sq_le (P : Parameters) (h : ScalarCertificate P H A B) (hraw : UniversalRawCubicBound H)
    (hquartic : UniversalCubicQuarticUnitSupport A B) (N : ℕ)
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) :
    GeneralWeighted.energy μ f (weight P) N ≤ P.C*‖f‖^2 := by
  have hb := actual_weighted_energy_le P h hraw hquartic N hμ (Lp.memLp f)
  rwa [←actualLp_norm_sq_eq_integral] at hb

end KLSConstantImprovement.RawCubicQuarticWeightedBudget
#print axioms KLSConstantImprovement.RawCubicQuarticWeightedBudget.actual_weighted_energy_small_degree
#print axioms KLSConstantImprovement.RawCubicQuarticWeightedBudget.actual_weighted_energy_le
#print axioms KLSConstantImprovement.RawCubicQuarticWeightedBudget.actual_weighted_energy_norm_sq_le

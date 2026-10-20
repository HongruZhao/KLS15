import KLSConstantImprovement.PositiveEnergyWeightedGenerator
import ActualCreationCenteredCubicSeed239

/-! A scalar-only certificate for the actual universal budget with arbitrary
positive degree energy multipliers and complete signed size-two refunds. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix
open scoped BigOperators
namespace KLSConstantImprovement.PositiveEnergyWeightedBudget
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

structure Parameters where
  K : ℝ
  C : ℝ
  c : ℝ
  young : ℕ → ℝ
  t : ℕ → ℝ
  alpha : ℕ → ℝ
  theta : ℕ → ℝ
  lambda : ℕ → ℝ

def weight (P : Parameters) (d : ℕ) : ℝ := PositiveEnergyWeightedDrift.weight P.K P.t d
def cost (P : Parameters) (d : ℕ) : ℝ :=
  PositiveEnergyWeightedGenerator.cost P.K P.C P.young P.t P.theta P.lambda d
def coefficient (P : Parameters) (d : ℕ) : ℝ :=
  PositiveEnergyWeightedGenerator.coefficient P.K P.C P.young P.t P.alpha P.theta P.lambda d
def head (P : Parameters) : ℝ :=
  PositiveEnergyWeightedGenerator.head P.K P.C P.young P.t P.alpha P.theta P.lambda

def headPolynomial (P : Parameters) (t : ℝ) : ℝ :=
  P.c*P.C-(P.c+head P)*(2*P.t 2/P.K^2)*(t^2*(CreationSeed239.seedV t)^2)-
    (P.c-coefficient P 3)*(P.t 3*CreationSeed239.B/P.K^3)*(1-t^2)

/-- Rational polynomial positivity discharges the inverse-barrier head condition. -/
theorem head_margin_of_polynomial (P : Parameters)
    (hp : ∀ t, t ∈ Icc (0 : ℝ) CreationSeed239.seedT → 0 < headPolynomial P t)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    (P.c+head P)*(2*P.t 2/P.K^2)*u+
      (P.c-coefficient P 3)*(P.t 3*CreationSeed239.B/P.K^3)*CreationSeed239.seedPhi u < P.c*P.C := by
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
  quadratic_payment : 3+PositiveEnergyWeightedDrift.kappa P.K P.young P.t P.lambda 2 ≤
    4*(PositiveEnergyWeightedGenerator.gamma P.K P.t P.theta 2)^2/(1-P.alpha 2)
  terminal_payment : ∀ (d : ℕ), 3 ≤ d →
    ((d : ℝ)+PositiveEnergyWeightedDrift.kappa P.K P.young P.t P.lambda d)*(1-P.alpha d) ≤ (d : ℝ)
  coefficient_lower : ∀ d, 4 ≤ d → P.c ≤ coefficient P d
  head_nonneg : 0 ≤ P.c+head P
  third_nonneg : 0 ≤ P.c-coefficient P 3
  head_margin : ∀ u, u ∈ Icc (0 : ℝ) 1 →
    (P.c+head P)*(2*P.t 2/P.K^2)*u+
      (P.c-coefficient P 3)*(P.t 3*CreationSeed239.B/P.K^3)*CreationSeed239.seedPhi u < P.c*P.C

theorem ScalarCertificate.C_nonneg {P : Parameters} (h : ScalarCertificate P) : 0 ≤ P.C :=
  (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (h.weight_positive 2 (by omega)).le) (sq_nonneg P.K)).trans h.base_budget

theorem ScalarCertificate.weight_nonneg {P : Parameters} (h : ScalarCertificate P)
    (d : ℕ) (hd : 2 ≤ d) : 0 ≤ weight P d :=
  (PositiveEnergyWeightedDrift.weight_positive h.K_positive P.t d (h.weight_positive d hd)).le

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
    (he2 : e 2 ≤ (2*P.t 2/P.K^2)*u)
    (he3 : e 3 ≤ (P.t 3*CreationSeed239.B/P.K^3)*CreationSeed239.seedPhi u)
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
    GeneralWeighted.energy μ f (weight P) N ≤ P.C*(∫ x, (f x)^2 ∂μ) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hi : 0 ≤ ∫ x, (f x)^2 ∂μ := integral_nonneg fun x => sq_nonneg _
  by_cases h2 : N = 2
  · subst N
    have hb := actualAppellEnergy_two_le_eight_integral hμ hf
    have hnorm : GeneralWeighted.energy μ f (weight P) 2 =
        weight P 2*actualAppellEnergy μ f 2 := by
      norm_num [GeneralWeighted.energy]
    rw [hnorm]
    calc
      _ ≤ weight P 2*(8*(∫ x, (f x)^2 ∂μ)) :=
        mul_le_mul_of_nonneg_left hb (h.weight_nonneg 2 (by omega))
      _ = (2*P.t 2/P.K^2)*(∫ x, (f x)^2 ∂μ) := by
        norm_num [weight,PositiveEnergyWeightedDrift.weight,CoupledEnergy.factorialWeight]
        field_simp
        ring
      _ ≤ P.C*(∫ x, (f x)^2 ∂μ) := mul_le_mul_of_nonneg_right h.base_budget hi
  · have hn : N < 2 := by omega
    have he : Finset.Icc 2 N = ∅ := Finset.Icc_eq_empty_of_lt hn
    simp only [GeneralWeighted.energy,he,Finset.sum_empty]
    exact mul_nonneg h.C_nonneg hi

/-- Original admissible laws and all actual L2 tests, in every finite degree.
Only the explicit scalar certificate is supplied by a profile. -/
theorem actual_weighted_energy_le (P : Parameters) (h : ScalarCertificate P) (N : ℕ)
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
      by_cases hsmall : N ≤ 2
      · exact actual_weighted_energy_small_degree P h hsmall hν hg
      have hN : 3 ≤ N := by omega
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
      have hgen := PositiveEnergyWeightedGenerator.actual_generator_coefficients_nonpos hμ' f₀
        hunit h.K_positive P.young P.t P.alpha P.theta P.lambda h.young_positive h.weight_positive
        h.alpha_nonneg h.alpha_lt_one h.theta_nonneg h.theta_le_one h.lambda_nonneg h.lambda_le_one
        h.lambda_boundary h.quadratic_payment h.terminal_payment N hN hprevious hstat hheat
      let u := actualAppellEnergy (μ' : Measure (Space n)) f₀ 2/8
      have hu : u ∈ Icc (0 : ℝ) 1 := by
        have hb := actualAppellEnergy_two_le_eight_norm_sq hμ' f₀
        rw [hunit] at hb
        dsimp only [u]
        constructor
        · exact div_nonneg (actualAppellEnergy_nonneg _ _ _) (by norm_num)
        · norm_num at hb ⊢
          linarith
      have he2 : weight P 2*
          actualAppellEnergy (μ' : Measure (Space n)) f₀ 2 ≤ (2*P.t 2/P.K^2)*u := by
        dsimp only [u]
        norm_num [weight,PositiveEnergyWeightedDrift.weight,CoupledEnergy.factorialWeight] <;> field_simp <;> ring_nf <;> exact le_rfl
      have he3 : weight P 3*
          actualAppellEnergy (μ' : Measure (Space n)) f₀ 3 ≤
          (P.t 3*CreationSeed239.B/P.K^3)*CreationSeed239.seedPhi u := by
        have hb := actual_appell_joint_cubic_seed_creation239 hμ' f₀ hunit
        change actualAppellEnergy (μ' : Measure (Space n)) f₀ 3 ≤
          (36*CreationSeed239.B)*CreationSeed239.seedPhi u at hb
        calc
          _ ≤ weight P 3*
              ((36*CreationSeed239.B)*CreationSeed239.seedPhi u) :=
            mul_le_mul_of_nonneg_left hb (h.weight_nonneg 3 (by omega))
          _ = _ := by
            norm_num [weight,PositiveEnergyWeightedDrift.weight,CoupledEnergy.factorialWeight] <;> field_simp <;> ring
      have hM : M < P.C := by
        apply finite_energy_sum_lt_budget P h
          (fun d => weight P d*
            actualAppellEnergy (μ' : Measure (Space n)) f₀ d) N hN
        · intro d hd
          exact mul_nonneg (h.weight_nonneg d (by have:=(Finset.mem_Icc.mp hd).1;omega))
            (actualAppellEnergy_nonneg _ _ _)
        · exact hu
        · exact he2
        · exact he3
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

theorem actual_weighted_energy_norm_sq_le (P : Parameters) (h : ScalarCertificate P) (N : ℕ)
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) :
    GeneralWeighted.energy μ f (weight P) N ≤ P.C*‖f‖^2 := by
  have hb := actual_weighted_energy_le P h N hμ (Lp.memLp f)
  rwa [←actualLp_norm_sq_eq_integral] at hb

end KLSConstantImprovement.PositiveEnergyWeightedBudget
#print axioms KLSConstantImprovement.PositiveEnergyWeightedBudget.head_margin_of_polynomial
#print axioms KLSConstantImprovement.PositiveEnergyWeightedBudget.actual_weighted_energy_le
#print axioms KLSConstantImprovement.PositiveEnergyWeightedBudget.actual_weighted_energy_norm_sq_le

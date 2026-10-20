import ActualWeightedGeneratorLowerSub15
import CoupledSub15HeadCertificate
import ActualAppellQuadraticSeed
import ActualSymmetricCenteredCubicSeed245

/-! The finite coupled Appell energy bound at K=67/5 and C=6/125.
The induction is on the final degree, so every proper cumulant contraction
is supplied by the previous universal weighted bound. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
open CoupledEnergy.NumericsSub15
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem actual_weighted_appell_energy_small_degree_sub15 {N : ℕ} (hN : N ≤ 2)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    actualWeightedAppellEnergy μ f K N ≤ (C)*(∫ x,(f x)^2 ∂μ) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hi : 0 ≤ ∫ x,(f x)^2 ∂μ := integral_nonneg fun x => sq_nonneg _
  by_cases h2 : N=2
  · subst N
    have hb := actualAppellEnergy_two_le_eight_integral hμ hf
    norm_num [actualWeightedAppellEnergy,K,C] at ⊢
    linarith
  · have hn : N < 2 := by omega
    have he : Finset.Icc 2 N=∅ := Finset.Icc_eq_empty_of_lt hn
    simp only [actualWeightedAppellEnergy,he,Finset.sum_empty]
    exact mul_nonneg C_positive.le hi


/-- The actual finite coupled energy bound. Every input is an original
admissible law and an actual L² test; maximum, drift, and induction are internal. -/
theorem actual_weighted_appell_energy_thirteen_four_le (N : ℕ)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    actualWeightedAppellEnergy μ f K N ≤ (C)*(∫ x,(f x)^2 ∂μ) := by
  have hall : ∀ N : ℕ, ∀ (ν : Measure (Space n)), admissibleMeasure ν →
      ∀ g : Space n → ℝ, MemLp g 2 ν →
      actualWeightedAppellEnergy ν g K N ≤ (C)*(∫ x,(g x)^2 ∂ν) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro ν hν g hg
      let : IsProbabilityMeasure ν := hν.isProb
      by_cases hsmall : N ≤ 2
      · exact actual_weighted_appell_energy_small_degree_sub15 hsmall hν hg
      have hN : 3 ≤ N := by omega
      let ν₀ : ProbabilityMeasure (Space n) := ⟨ν,hν.isProb⟩
      obtain ⟨μ',hμ',c,hunit,hglobal,hstat,hheat⟩ :=
        exists_actual_centered_weighted_maximum_energy_inequality (N:=N) (K:=K)
          (μ₀:=ν₀) K_positive hν
      let p := polynomialLp hμ'.logConcave (boundedDegreePolynomial c)
      let M := actualWeightedAppellEnergy (μ' : Measure (Space n)) p K N
      have hprevious : ∀ a : Space n → ℝ, MemLp a 2 (μ' : Measure (Space n)) →
          actualWeightedAppellEnergy (μ' : Measure (Space n)) a K (N-1) ≤
            (C)*(∫ x,(a x)^2 ∂(μ' : Measure (Space n))) := by
        intro a ha
        exact ih (N-1) (by omega) (μ' : Measure (Space n)) hμ' a ha
      have hgen := actual_weighted_generator_coefficients_nonpos_sub15 hμ' p hunit N (by omega)
        hprevious hstat hheat
      let u := actualAppellEnergy (μ' : Measure (Space n)) p 2/8
      have hu : u∈Icc (0 : ℝ) 1 := by
        have hb := actualAppellEnergy_two_le_eight_norm_sq hμ' p
        rw [hunit] at hb
        dsimp only [u]
        constructor
        · exact div_nonneg (actualAppellEnergy_nonneg _ _ _) (by norm_num)
        · norm_num at hb ⊢
          linarith
      have he2 : (((K : ℝ)^2*(Nat.factorial 2 : ℝ)^2)⁻¹*
          actualAppellEnergy (μ' : Measure (Space n)) p 2) ≤ (2/K^2)*u := by
        dsimp only [u]
        norm_num [K]
        ring_nf
        rfl
      have he3 : (((K : ℝ)^3*(Nat.factorial 3 : ℝ)^2)⁻¹*
          actualAppellEnergy (μ' : Measure (Space n)) p 3) ≤
          (SymmetricCenteredSeed245.B/K^3)*SymmetricCenteredSeed245.seedPhi u := by
        have hb := actual_appell_joint_cubic_seed_symmetric_245 hμ' p hunit
        dsimp only [u]
        norm_num [K,SymmetricCenteredSeed245.B] at hb ⊢
        linarith
      have hgen' : (∑ d∈Finset.Icc 3 N,coefficient d*
          (((K : ℝ)^d*(d.factorial : ℝ)^2)⁻¹*
            actualAppellEnergy (μ' : Measure (Space n)) p d))-
          head*(((K : ℝ)^2*(Nat.factorial 2 : ℝ)^2)⁻¹*
            actualAppellEnergy (μ' : Measure (Space n)) p 2)≤0 := hgen
      have hM : M < (C : ℝ) := by
        apply finite_energy_sum_lt_budget
          (fun d => ((K : ℝ)^d*(d.factorial : ℝ)^2)⁻¹*
            actualAppellEnergy (μ' : Measure (Space n)) p d) N hN
        · intro d hd
          exact mul_nonneg (inv_nonneg.mpr
            (mul_nonneg (pow_nonneg K_positive.le _) (sq_nonneg _)))
            (actualAppellEnergy_nonneg _ _ _)
        · exact hu
        · exact he2
        · exact he3
        · exact hgen'
      have hnorm : ‖hg.toLp g‖^2=(∫ x,(g x)^2 ∂ν) := by
        rw [actualLp_norm_sq_eq_integral]
        exact integral_congr_ae (hg.coeFn_toLp.fun_comp (fun t : ℝ => t^2))
      calc
        actualWeightedAppellEnergy ν g K N =
            actualWeightedAppellEnergy ν (hg.toLp g) K N :=
          (actualWeightedAppellEnergy_congr_ae hg.coeFn_toLp K N).symm
        _ ≤ M*‖hg.toLp g‖^2 := hglobal ν₀ hν (hg.toLp g)
        _ ≤ (C)*‖hg.toLp g‖^2 :=
          mul_le_mul_of_nonneg_right hM.le (sq_nonneg _)
        _ = (C)*(∫ x,(g x)^2 ∂ν) := by rw [hnorm]
  exact hall N μ hμ f hf

theorem actual_weighted_appell_energy_thirteen_four_norm_sq_le (N : ℕ)
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) :
    actualWeightedAppellEnergy μ f K N ≤ (C)*‖f‖^2 := by
  have hb := actual_weighted_appell_energy_thirteen_four_le N hμ (Lp.memLp f)
  rwa [←actualLp_norm_sq_eq_integral] at hb

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_weighted_appell_energy_small_degree_sub15

#print axioms KLS.DeterministicBridgeNext.actual_weighted_appell_energy_thirteen_four_le
#print axioms KLS.DeterministicBridgeNext.actual_weighted_appell_energy_thirteen_four_norm_sq_le

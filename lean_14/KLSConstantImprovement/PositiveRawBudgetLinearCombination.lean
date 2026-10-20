import Mathlib

/-! Exact rescaling and nonnegative linear combinations of raw weighted
budgets. No probabilistic or analytic premise is introduced. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.PositiveRawBudgetLinearCombination
set_option maxHeartbeats 3000000

theorem term_identity (K L a : ℝ) (t u E : ℕ → ℝ)
    (hK : K≠0) (hL : L≠0) (d : ℕ) :
    (t d+a*u d*(K/L)^d)*K⁻¹^d*E d/(d.factorial : ℝ)^2 =
      t d*K⁻¹^d*E d/(d.factorial : ℝ)^2+
        a*(u d*L⁻¹^d*E d/(d.factorial : ℝ)^2) := by
  have he : (K/L)^d*K⁻¹^d=L⁻¹^d := by
    rw [←mul_pow]
    congr 1
    field_simp [hK,hL]
  calc
    _ = t d*K⁻¹^d*E d/(d.factorial : ℝ)^2+
        a*u d*((K/L)^d*K⁻¹^d)*E d/(d.factorial : ℝ)^2 := by ring
    _ = _ := by rw [he];ring

theorem sum_identity (K L a : ℝ) (t u E : ℕ → ℝ)
    (hK : K≠0) (hL : L≠0) (N : ℕ) :
    (∑ d ∈ Finset.Icc 2 N,(t d+a*u d*(K/L)^d)*K⁻¹^d*E d/(d.factorial : ℝ)^2) =
      (∑ d ∈ Finset.Icc 2 N,t d*K⁻¹^d*E d/(d.factorial : ℝ)^2)+
        a*(∑ d ∈ Finset.Icc 2 N,u d*L⁻¹^d*E d/(d.factorial : ℝ)^2) := by
  simp_rw [term_identity K L a t u E hK hL]
  rw [Finset.sum_add_distrib,←Finset.mul_sum]

theorem sum_le_of_two_budgets (K L C D a mass : ℝ) (t u E : ℕ → ℝ)
    (hK : K≠0) (hL : L≠0) (ha : 0 ≤ a) (N : ℕ)
    (ht : (∑ d ∈ Finset.Icc 2 N,t d*K⁻¹^d*E d/(d.factorial : ℝ)^2) ≤ C*mass)
    (hu : (∑ d ∈ Finset.Icc 2 N,u d*L⁻¹^d*E d/(d.factorial : ℝ)^2) ≤ D*mass) :
    (∑ d ∈ Finset.Icc 2 N,(t d+a*u d*(K/L)^d)*K⁻¹^d*E d/(d.factorial : ℝ)^2) ≤
      (C+a*D)*mass := by
  rw [sum_identity K L a t u E hK hL]
  calc
    _ ≤ C*mass+a*(D*mass) := add_le_add ht (mul_le_mul_of_nonneg_left hu ha)
    _ = _ := by ring

theorem sum_mono (K : ℝ) (t u E : ℕ → ℝ) (hK : 0 ≤ K) (N : ℕ)
    (htu : ∀ d,2 ≤ d → t d ≤ u d) (hE : ∀ d,2 ≤ d → 0 ≤ E d) :
    (∑ d ∈ Finset.Icc 2 N,t d*K⁻¹^d*E d/(d.factorial : ℝ)^2) ≤
      (∑ d ∈ Finset.Icc 2 N,u d*K⁻¹^d*E d/(d.factorial : ℝ)^2) := by
  apply Finset.sum_le_sum
  intro d hd
  have hd2 := (Finset.mem_Icc.mp hd).1
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (htu d hd2) (pow_nonneg (inv_nonneg.mpr hK) d))
      (hE d hd2)) (sq_nonneg _)

end KLSConstantImprovement.PositiveRawBudgetLinearCombination
#print axioms KLSConstantImprovement.PositiveRawBudgetLinearCombination.sum_identity
#print axioms KLSConstantImprovement.PositiveRawBudgetLinearCombination.sum_le_of_two_budgets
#print axioms KLSConstantImprovement.PositiveRawBudgetLinearCombination.sum_mono

import Mathlib

/-! A finite Schur row estimate with the actual symmetric Gram retained. -/
noncomputable section
open scoped BigOperators
namespace KLSImprovement.FiniteGram
set_option maxHeartbeats 1000000

theorem weighted_pair_young (a b g : ℝ) :
    2*(a*b*g) ≤ (a^2+b^2)*|g| := by
  by_cases hg : 0 ≤ g
  · rw [abs_of_nonneg hg]
    nlinarith [mul_nonneg (sq_nonneg (a-b)) hg]
  · rw [abs_of_neg (lt_of_not_ge hg)]
    nlinarith [mul_nonneg (sq_nonneg (a+b)) (neg_nonneg.mpr (le_of_not_ge hg))]

theorem symmetric_abs_row_quadratic_bound {ι : Type*} [Fintype ι]
    (G : ι → ι → ℝ) (hG : ∀ i j, G i j = G j i) {C : ℝ}
    (hrow : ∀ i, ∑ j, |G i j| ≤ C) (t : ι → ℝ) :
    (∑ i, ∑ j, t i*t j*G i j) ≤ C*(∑ i, (t i)^2) := by
  have hp : (∑ i, ∑ j, 2*(t i*t j*G i j)) ≤
      ∑ i, ∑ j, ((t i)^2+(t j)^2)*|G i j| :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => weighted_pair_young _ _ _))
  have hsym : (∑ i, ∑ j, (t j)^2*|G i j|) =
      ∑ i, ∑ j, (t i)^2*|G i j| := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hG j i]
  have hb : (∑ i, ∑ j, (t i)^2*|G i j|) ≤ C*(∑ i, (t i)^2) := by
    simp_rw [←Finset.mul_sum]
    calc
      _ ≤ ∑ i, (t i)^2*C := Finset.sum_le_sum
        (fun i _ => mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg _))
      _ = _ := by rw [←Finset.sum_mul, mul_comm]
  simp_rw [add_mul, Finset.sum_add_distrib] at hp
  rw [hsym] at hp
  simp_rw [←Finset.mul_sum] at hp hb
  nlinarith

end KLSImprovement.FiniteGram
#print axioms KLSImprovement.FiniteGram.symmetric_abs_row_quadratic_bound

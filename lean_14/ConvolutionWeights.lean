import Mathlib

/-! Exact elementary convolution weights for the exceptional second
coefficient. This module contains no measure or Appell assumptions. -/
noncomputable section
open scoped BigOperators
namespace ConvolutionWeights

def exceptionalWeight (e : ℝ) (a : ℕ) : ℝ := if a = 2 then e else 1

theorem sum_indices {n : ℕ} (hn : 2 ≤ n) :
    ∑ a ∈ Finset.Ico 2 n, (a : ℝ) = (n : ℝ)*((n : ℝ)-1)/2-1 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [Finset.sum_Ico_succ_top hn, ih]
      push_cast
      ring

theorem reflected_sum {n : ℕ} (hn : 2 ≤ n) :
    ∑ a ∈ Finset.Icc 2 (n-1), ((n-a+1 : ℕ) : ℝ) =
      (n : ℝ)*((n : ℝ)-1)/2-1 := by
  have hset : Finset.Icc 2 (n-1) = Finset.Ico 2 n := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hset]
  have heq : ∑ a ∈ Finset.Ico 2 n, ((n-a+1 : ℕ) : ℝ) =
      ∑ a ∈ Finset.Ico 2 n, ((n+1-a : ℕ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro a ha
    congr 1
    simp only [Finset.mem_Ico] at ha
    omega
  rw [heq]
  have hr := Finset.sum_Ico_reflect (fun a : ℕ => (a : ℝ)) 2
    (m := n) (n := n+1) (by omega : n ≤ n+1+1)
  have hlow : n+1+1-n = 2 := by omega
  have hhigh : n+1+1-2 = n := by omega
  rw [hlow, hhigh] at hr
  rw [hr]
  exact sum_indices hn

theorem term_expansion {n a : ℕ} (hn : 4 ≤ n)
    (ha : a ∈ Finset.Icc 2 (n-1)) (e : ℝ) :
    ((n-a+1 : ℕ) : ℝ)*exceptionalWeight e a*
      exceptionalWeight e (n-a+1) =
      ((n-a+1 : ℕ) : ℝ) +
      (if a = 2 then ((n-1 : ℕ) : ℝ)*(e-1) else 0) +
      (if a = n-1 then 2*(e-1) else 0) := by
  simp only [Finset.mem_Icc] at ha
  by_cases h2 : a = 2
  · subst a
    have hnt : n-2+1 = n-1 := by omega
    have hne : n-1 ≠ 2 := by omega
    have hneq : (2 : ℕ) ≠ n-1 := by omega
    simp [exceptionalWeight, hnt, hne, hneq]
    ring
  · by_cases htop : a = n-1
    · subst a
      have hnt : n-(n-1)+1 = 2 := by omega
      simp [exceptionalWeight, h2, hnt]
      ring
    · have hb : n-a+1 ≠ 2 := by omega
      simp [exceptionalWeight, h2, htop, hb]

theorem exact_sum {n : ℕ} (hn : 4 ≤ n) (e : ℝ) :
    ∑ a ∈ Finset.Icc 2 (n-1),
      ((n-a+1 : ℕ) : ℝ)*exceptionalWeight e a*
        exceptionalWeight e (n-a+1) =
      (n : ℝ)*((n : ℝ)-1)/2-1 + ((n : ℝ)+1)*(e-1) := by
  have h2 : 2 ∈ Finset.Icc 2 (n-1) := by
    simp only [Finset.mem_Icc]
    omega
  have ht : n-1 ∈ Finset.Icc 2 (n-1) := by
    simp only [Finset.mem_Icc]
    omega
  have he : (∑ a ∈ Finset.Icc 2 (n-1),
      ((n-a+1 : ℕ) : ℝ)*exceptionalWeight e a*
        exceptionalWeight e (n-a+1)) =
      ∑ a ∈ Finset.Icc 2 (n-1),
        (((n-a+1 : ℕ) : ℝ) +
          (if a = 2 then ((n-1 : ℕ) : ℝ)*(e-1) else 0) +
          (if a = n-1 then 2*(e-1) else 0)) := by
    apply Finset.sum_congr rfl
    intro a ha
    exact term_expansion hn ha e
  rw [he, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', h2, ht, if_true]
  rw [reflected_sum (by omega : 2 ≤ n)]
  rw [Nat.cast_sub (by omega : 1 ≤ n)]
  norm_num
  ring

theorem exact_sum_three (e : ℝ) :
    ∑ a ∈ Finset.Icc 2 (3-1),
      ((3-a+1 : ℕ) : ℝ)*exceptionalWeight e a*
        exceptionalWeight e (3-a+1) = 2*e^2 := by
  norm_num [exceptionalWeight, Finset.sum_Icc_succ_top]
  ring

#print axioms exact_sum
#print axioms exact_sum_three
end ConvolutionWeights

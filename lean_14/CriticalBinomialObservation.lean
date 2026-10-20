import NonnegativeMatrixSchur

/-! A uniform half bound for every finite critical binomial observation
matrix. The actual all-degree exponential Appell/Laguerre correspondence
is a separate formal obligation; this theorem is about the stated matrix. -/
noncomputable section
open scoped BigOperators
namespace KLSImprovement.CriticalBinomial
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def choosePrefix (n k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k+1), (n.choose j : ℝ)
def columnPrefix (M k : ℕ) : ℝ :=
  ∑ n ∈ Finset.range M, (n.choose k : ℝ)/(2:ℝ)^(n+1)

theorem choosePrefix_step (n k : ℕ) :
    choosePrefix n (k+1) = choosePrefix n k+(n.choose (k+1):ℝ) := by
  simp [choosePrefix, Finset.sum_range_succ]

theorem choosePrefix_succ (n k : ℕ) :
    choosePrefix (n+1) k = 2*choosePrefix n k-(n.choose k:ℝ) := by
  induction k with
  | zero => norm_num [choosePrefix]
  | succ k ih =>
    rw [choosePrefix_step, choosePrefix_step, ih, Nat.choose_succ_succ, Nat.cast_add]
    ring

theorem choosePrefix_zero (k : ℕ) : choosePrefix 0 k = 1 := by
  rw [choosePrefix, Finset.sum_range_succ']
  simp

theorem column_prefix_identity (M k : ℕ) :
    columnPrefix M k+choosePrefix M k/(2:ℝ)^M = 1 := by
  induction M with
  | zero => simp [columnPrefix, choosePrefix_zero]
  | succ M ih =>
    have hs : columnPrefix (M+1) k = columnPrefix M k+
        (M.choose k:ℝ)/(2:ℝ)^(M+1) := by
      simp [columnPrefix, Finset.sum_range_succ]
    rw [hs, choosePrefix_succ, pow_succ]
    calc
      _ = columnPrefix M k+choosePrefix M k/(2:ℝ)^M := by
        field_simp
        ring
      _ = 1 := ih

theorem column_prefix_le_one (M k : ℕ) : columnPrefix M k ≤ 1 := by
  have h := column_prefix_identity M k
  have hn : 0 ≤ choosePrefix M k/(2:ℝ)^M := by
    apply div_nonneg _ (by positivity)
    exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  linarith

def criticalMatrix (M : ℕ) (n k : Fin M) : ℝ :=
  (n.val.choose k.val:ℝ)/(2:ℝ)^(n.val+1)

theorem criticalMatrix_nonneg (M : ℕ) (n k : Fin M) :
    0 ≤ criticalMatrix M n k := by
  unfold criticalMatrix
  positivity

theorem criticalMatrix_row_sum (M : ℕ) (n : Fin M) :
    (∑ k, criticalMatrix M n k) = 1/2 := by
  have he : (∑ k ∈ Finset.range M, (n.val.choose k:ℝ)) =
      ∑ k ∈ Finset.range (n.val+1), (n.val.choose k:ℝ) := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro k hk hkn
    have hn : n.val < k := by
      simp only [Finset.mem_range, not_lt] at hkn
      omega
    simp [Nat.choose_eq_zero_of_lt hn]
  have hchoose : (∑ k ∈ Finset.range (n.val+1), (n.val.choose k:ℝ)) =
      (2:ℝ)^n.val := by exact_mod_cast Nat.sum_range_choose n.val
  simp only [criticalMatrix, ←Finset.sum_div]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (n.val.choose k:ℝ)) M,
    he, hchoose, pow_succ]
  field_simp

theorem criticalMatrix_column_le_one (M : ℕ) (k : Fin M) :
    (∑ n, criticalMatrix M n k) ≤ 1 := by
  unfold criticalMatrix
  rw [Fin.sum_univ_eq_sum_range
    (fun n : ℕ => (n.choose k.val:ℝ)/(2:ℝ)^(n+1)) M]
  exact column_prefix_le_one M k.val

theorem critical_binomial_square_sum_le_half (M : ℕ) (c : Fin M → ℝ) :
    (∑ n, (∑ k, criticalMatrix M n k*c k)^2) ≤
      (1/2:ℝ)*(∑ k, (c k)^2) := by
  simpa using KLSImprovement.NonnegativeSchur.finite_row_column_square_bound
    (criticalMatrix M) (R:=1/2) (C:=1) (by norm_num)
    (criticalMatrix_nonneg M) (fun n => (criticalMatrix_row_sum M n).le)
    (criticalMatrix_column_le_one M) c

theorem critical_binomial_degrees_ge_two_le_half (M : ℕ) (c : Fin M → ℝ) :
    (∑ n : Fin M, if n.val=0 then 0 else (∑ k, criticalMatrix M n k*c k)^2) ≤
      (1/2:ℝ)*(∑ k, (c k)^2) := by
  apply le_trans _ (critical_binomial_square_sum_le_half M c)
  apply Finset.sum_le_sum
  intro n _
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

end KLSImprovement.CriticalBinomial
#print axioms KLSImprovement.CriticalBinomial.column_prefix_identity
#print axioms KLSImprovement.CriticalBinomial.criticalMatrix_row_sum
#print axioms KLSImprovement.CriticalBinomial.critical_binomial_square_sum_le_half
#print axioms KLSImprovement.CriticalBinomial.critical_binomial_degrees_ge_two_le_half

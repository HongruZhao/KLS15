import Mathlib

/-! Pure growth exclusion for a selected nonincreasing ratio path.
All-rate fixed-geometric terminal bounds rule out a limiting ratio above1.
This draft has not been compiled; no actual orbit realization is asserted. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.GeometricTerminalGrowthExclusion

def P (r : ℕ → ℝ) (n : ℕ) : ℝ := ∏ k ∈ Finset.range n,r (k+1)

@[simp] theorem P_zero (r : ℕ → ℝ) : P r 0=1 := by simp [P]

theorem P_succ (r : ℕ → ℝ) (n : ℕ) :
    P r (n+1)=P r n*r (n+1) := by
  simp only [P,Finset.prod_range_succ]

theorem P_one_le (r : ℕ → ℝ) (h1 : ∀ n : ℕ,1 ≤ r n) (n : ℕ) :
    1 ≤ P r n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [P_succ]
    calc
      1 ≤ P r n := ih
      _ = P r n*1 := by ring
      _ ≤ P r n*r (n+1) :=
        mul_le_mul_of_nonneg_left (h1 (n+1)) (zero_le_one.trans ih)

theorem P_nonnegative (r : ℕ → ℝ) (h1 : ∀ n : ℕ,1 ≤ r n) (n : ℕ) :
    0 ≤ P r n := zero_le_one.trans (P_one_le r h1 n)

theorem P_monotone (r : ℕ → ℝ) (h1 : ∀ n : ℕ,1 ≤ r n) : Monotone (P r) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [P_succ]
  have hh := mul_le_mul_of_nonneg_left (h1 (n+1)) (P_nonnegative r h1 n)
  simpa only [mul_one] using hh

theorem pow_le_P_of_ratio_lower
    (r : ℕ → ℝ) (h1 : ∀ n : ℕ,1 ≤ r n) (q : ℝ) (hq : 0 ≤ q)
    (hqr : ∀ n : ℕ,q ≤ r n) (n : ℕ) :
    q^n ≤ P r n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,P_succ]
    exact mul_le_mul ih (hqr (n+1)) hq (P_nonnegative r h1 n)

/-- Every ratio threshold q>1 is eventually reached. Antitonicity is used
only to turn failure of eventual entry into a uniform lower ratio q. -/
theorem eventual_ratio_le
    (r : ℕ → ℝ) (C : ℝ) (hanti : Antitone r)
    (h1 : ∀ n : ℕ,1 ≤ r n)
    (hterminal : ∀ ρ : ℝ,1 < ρ → ∃ τ : ℝ,0 < τ ∧
      ∀ n : ℕ,P r n*(τ/ρ^(n+2))*max 0 (r n-ρ) ≤ C) :
    ∀ q : ℝ,1 < q → ∃ N : ℕ,∀ n : ℕ,N ≤ n → r n ≤ q := by
  have power_identity (u v t : ℝ) (hv : v ≠ 0) (n : ℕ) :
      (t * (u - v) / v ^ 2) * (u / v) ^ n =
        u ^ n * (t / v ^ (n + 2)) * (u - v) := by
    rw [div_pow u v n, pow_add v n 2]
    field_simp [hv, pow_ne_zero n hv] <;> ring
  intro q hq
  by_contra hnone
  have hall : ∀ n : ℕ,q < r n := by
    intro n
    by_contra hn
    have hn' : r n ≤ q := le_of_not_gt hn
    exact hnone ⟨n,fun m hnm => (hanti hnm).trans hn'⟩
  let ρ : ℝ := (q+1)/2
  have hρ1 : 1 < ρ := by dsimp only [ρ]; linarith
  have hρq : ρ < q := by dsimp only [ρ]; linarith
  have hρ0 : 0 < ρ := by linarith
  have hδ : 0 < q-ρ := sub_pos.mpr hρq
  obtain ⟨τ,hτ,hcap⟩ := hterminal ρ hρ1
  let H : ℝ := τ*(q-ρ)/ρ^2
  have hH : 0 < H :=
    div_pos (mul_pos hτ hδ) (sq_pos_of_pos hρ0)
  have hP (n : ℕ) : q^n ≤ P r n :=
    pow_le_P_of_ratio_lower r h1 q (by linarith) (fun i => (hall i).le) n
  have hid (n : ℕ) :
      H*(q/ρ)^n=q^n*(τ/ρ^(n+2))*(q-ρ) := by
    exact power_identity q ρ τ (ne_of_gt hρ0) n
  have hbound (n : ℕ) : H*(q/ρ)^n ≤ C := by
    have hfac : 0 ≤ τ/ρ^(n+2) := by positivity
    have hmax : q-ρ ≤ max 0 (r n-ρ) := by
      have hh : q-ρ ≤ r n-ρ := by linarith [hall n]
      exact hh.trans (le_max_right _ _)
    calc
      H*(q/ρ)^n=q^n*(τ/ρ^(n+2))*(q-ρ) := hid n
      _ ≤ P r n*(τ/ρ^(n+2))*(q-ρ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hP n) hfac) hδ.le
      _ ≤ P r n*(τ/ρ^(n+2))*max 0 (r n-ρ) :=
        mul_le_mul_of_nonneg_left hmax
          (mul_nonneg (P_nonnegative r h1 n) hfac)
      _ ≤ C := hcap n
  have hratio : 1 < q/ρ :=
    (lt_div_iff₀ hρ0).2 (by simpa using hρq)
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (C/H) hratio
  have hbig : C < H*(q/ρ)^n := by
    have hh := (div_lt_iff₀ hH).mp hn
    nlinarith only [hh]
  exact (not_lt_of_ge (hbound n)) hbig

/-- The ratio conclusion gives a positive all-rate product envelope.
The finite prefix multiplier is simply P_N, with no prefix division. -/
theorem product_subexponential
    (r : ℕ → ℝ) (C : ℝ) (hanti : Antitone r)
    (h1 : ∀ n : ℕ,1 ≤ r n)
    (hterminal : ∀ ρ : ℝ,1 < ρ → ∃ τ : ℝ,0 < τ ∧
      ∀ n : ℕ,P r n*(τ/ρ^(n+2))*max 0 (r n-ρ) ≤ C) :
    ∀ q : ℝ,1 < q → ∃ M : ℝ,0 < M ∧
      ∀ n : ℕ,P r n ≤ M*q^n := by
  intro q hq
  obtain ⟨N,hN⟩ := eventual_ratio_le r C hanti h1 hterminal q hq
  refine ⟨P r N,lt_of_lt_of_le zero_lt_one (P_one_le r h1 N),?_⟩
  have hmono := P_monotone r h1
  intro n
  induction n with
  | zero => simpa using P_one_le r h1 N
  | succ n ih =>
    by_cases hsmall : n+1 ≤ N
    · have hpow : (1 : ℝ) ≤ q^(n+1) := one_le_pow₀ hq.le
      calc
        P r (n+1) ≤ P r N := hmono hsmall
        _ = P r N*1 := by ring
        _ ≤ P r N*q^(n+1) :=
          mul_le_mul_of_nonneg_left hpow (P_nonnegative r h1 N)
    · have hnext : r (n+1) ≤ q := hN (n+1) (by omega)
      rw [P_succ,pow_succ]
      calc
        P r n*r (n+1) ≤ P r n*q :=
          mul_le_mul_of_nonneg_left hnext (P_nonnegative r h1 n)
        _ ≤ (P r N*q^n)*q :=
          mul_le_mul_of_nonneg_right ih (by linarith)
        _ = P r N*(q^n*q) := by ring

end KLSConstantImprovement.GeometricTerminalGrowthExclusion

#print axioms KLSConstantImprovement.GeometricTerminalGrowthExclusion.eventual_ratio_le
#print axioms KLSConstantImprovement.GeometricTerminalGrowthExclusion.product_subexponential

import Mathlib
import Mathlib.RingTheory.Polynomial.Bernstein

/-! Generic positivity of finite Bernstein certificates, including endpoints.
No polynomial coefficient data or KLS assertion is assumed or introduced here. -/
noncomputable section
open scoped BigOperators
open Set
namespace KLSBelow25.BernsteinInterval

def bernsteinSum (n : ℕ) (b : Fin (n+1) → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin (n+1), b i*(Nat.choose n i : ℝ)*x^(i : ℕ)*(1-x)^(n-i)

theorem bernsteinSum_pos {n : ℕ} {b : Fin (n+1) → ℝ} {x : ℝ}
    (hb : ∀ i, 0 < b i) (hx : x ∈ Icc (0 : ℝ) 1) :
    0 < bernsteinSum n b x := by
  have hnonneg (i : Fin (n+1)) :
      0 ≤ b i*(Nat.choose n i : ℝ)*x^(i : ℕ)*(1-x)^(n-i) := by
    have := (hb i).le
    have := hx.1
    have : 0 ≤ 1-x := by linarith [hx.2]
    positivity
  unfold bernsteinSum
  apply Finset.sum_pos'
  · intro i _
    exact hnonneg i
  · by_cases hlt : x < 1
    · refine ⟨0, Finset.mem_univ _, ?_⟩
      simp only [Fin.val_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
        pow_zero, Nat.sub_zero]
      exact mul_pos (hb 0) (pow_pos (by linarith) _)
    · have heq : x=1 := le_antisymm hx.2 (le_of_not_gt hlt)
      refine ⟨Fin.last n, Finset.mem_univ _, ?_⟩
      simp only [Fin.val_last, Nat.choose_self, Nat.cast_one, mul_one, heq,
        one_pow, Nat.sub_self, pow_zero]
      exact hb (Fin.last n)

theorem scaledBernsteinSum_pos {n : ℕ} {b : Fin (n+1) → ℝ} {x T : ℝ}
    (hT : 0 < T) (hb : ∀ i, 0 < b i) (hx : x ∈ Icc (0 : ℝ) T) :
    0 < bernsteinSum n b (x/T) := by
  exact bernsteinSum_pos hb ⟨div_nonneg hx.1 hT.le, (div_le_one hT).mpr hx.2⟩

theorem positive_of_scaled_representation {n : ℕ} {b : Fin (n+1) → ℝ}
    {p : ℝ → ℝ} {T : ℝ} (hT : 0 < T) (hb : ∀ i, 0 < b i)
    (hrep : ∀ x, p x=bernsteinSum n b (x/T)) :
    ∀ x ∈ Icc (0 : ℝ) T, 0 < p x := by
  intro x hx
  rw [hrep]
  exact scaledBernsteinSum_pos hT hb hx

def unnormalizedSum (n : ℕ) (b : Fin (n+1) → ℝ) (T x : ℝ) : ℝ :=
  ∑ i : Fin (n+1), b i*x^(i : ℕ)*(T-x)^(n-i)

theorem unnormalizedSum_pos {n : ℕ} {b : Fin (n+1) → ℝ} {x T : ℝ}
    (hT : 0 < T) (hb : ∀ i, 0 < b i) (hx : x ∈ Icc (0 : ℝ) T) :
    0 < unnormalizedSum n b T x := by
  have hnonneg (i : Fin (n+1)) : 0 ≤ b i*x^(i : ℕ)*(T-x)^(n-i) := by
    have := (hb i).le
    have := hx.1
    have : 0 ≤ T-x := by linarith [hx.2]
    positivity
  unfold unnormalizedSum
  apply Finset.sum_pos'
  · intro i _
    exact hnonneg i
  · by_cases hlt : x < T
    · refine ⟨0, Finset.mem_univ _, ?_⟩
      simp only [Fin.val_zero, pow_zero, mul_one, Nat.sub_zero]
      exact mul_pos (hb 0) (pow_pos (by linarith) _)
    · have heq : x=T := le_antisymm hx.2 (le_of_not_gt hlt)
      refine ⟨Fin.last n, Finset.mem_univ _, ?_⟩
      simp only [Fin.val_last, heq, Nat.sub_self, pow_zero, mul_one]
      exact mul_pos (hb (Fin.last n)) (pow_pos hT _)

def rationalBernsteinPolynomial (n : ℕ) (b : Fin (n+1) → ℚ) : Polynomial ℚ :=
  ∑ i : Fin (n+1), Polynomial.C (b i)*bernsteinPolynomial ℚ n i

theorem rationalBernsteinPolynomial_eval (n : ℕ) (b : Fin (n+1) → ℚ) (x : ℝ) :
    Polynomial.eval₂ (algebraMap ℚ ℝ) x (rationalBernsteinPolynomial n b) =
      bernsteinSum n (fun i => (b i : ℝ)) x := by
  unfold rationalBernsteinPolynomial
  rw [Polynomial.eval₂_finsetSum]
  unfold bernsteinSum
  apply Finset.sum_congr rfl
  intro i _
  simp [bernsteinPolynomial, mul_assoc]

theorem rational_polynomial_positive_of_scaled_representation
    {n : ℕ} {b : Fin (n+1) → ℚ} {p : Polynomial ℚ} {T : ℚ}
    (hT : 0 < T) (hb : ∀ i, 0 < b i)
    (hrep : p.comp (Polynomial.C T*Polynomial.X)=rationalBernsteinPolynomial n b) :
    ∀ x ∈ Icc (0 : ℝ) (T : ℝ), 0 < Polynomial.eval₂ (algebraMap ℚ ℝ) x p := by
  intro x hx
  have ht : (0 : ℝ)<T := by exact_mod_cast hT
  have hbc : ∀ i, (0 : ℝ)<(b i : ℝ) := by intro i; exact_mod_cast hb i
  have he := congrArg (Polynomial.eval₂ (algebraMap ℚ ℝ) (x/(T : ℝ))) hrep
  rw [Polynomial.eval₂_comp, rationalBernsteinPolynomial_eval] at he
  have hi : Polynomial.eval₂ (algebraMap ℚ ℝ) (x/(T : ℝ))
      (Polynomial.C T*Polynomial.X)=x := by
    simp
    field_simp
  rw [hi] at he
  rw [he]
  exact scaledBernsteinSum_pos ht hbc hx

end KLSBelow25.BernsteinInterval
end

#print axioms KLSBelow25.BernsteinInterval.bernsteinSum_pos
#print axioms KLSBelow25.BernsteinInterval.scaledBernsteinSum_pos
#print axioms KLSBelow25.BernsteinInterval.positive_of_scaled_representation
#print axioms KLSBelow25.BernsteinInterval.unnormalizedSum_pos
#print axioms KLSBelow25.BernsteinInterval.rational_polynomial_positive_of_scaled_representation

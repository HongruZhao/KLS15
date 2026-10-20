import QuinticFiniteCriterion
import Mathlib.Data.Nat.Choose.Cast
import ConvolutionWeights

/-! Concrete coefficient constants and exact convolution normalization.
Only degrees at least two occur in the convolution; degree one is set
separately to one in the paper. -/
noncomputable section
namespace Quintic24886

def C : ℝ := B/K
def exceptionalScale : ℝ := Real.sqrt (2/C)
def exceptionalWeight (d : ℕ) : ℝ := if d=2 then exceptionalScale else 1
def coefficientH (d : ℕ) : ℝ :=
  C*K^(d-2)*(Nat.factorial d : ℝ)^2*(exceptionalWeight d)^2
def coefficientD (ell : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 2 (ell-1),
    (ell.choose a : ℝ)*Real.sqrt (coefficientH a * coefficientH (ell-a+1))

theorem C_positive : 0 < C := by norm_num [C,B,K]
theorem K_positive : 0 < K := by norm_num [K]
theorem exceptionalScale_positive : 0 < exceptionalScale := by
  exact Real.sqrt_pos.mpr (div_pos (by norm_num) C_positive)
theorem exceptionalScale_sq : exceptionalScale^2 = 2/C :=
  Real.sq_sqrt (by positivity [C_positive])
theorem exceptionalWeight_positive (d : ℕ) : 0 < exceptionalWeight d := by
  unfold exceptionalWeight
  split_ifs <;> first | exact exceptionalScale_positive | norm_num
theorem coefficientH_positive (d : ℕ) : 0 < coefficientH d := by
  unfold coefficientH
  positivity [C_positive, K_positive, exceptionalWeight_positive d]
theorem r_sq_mul_K : r^2*K=C := by norm_num [r,K,C,B]

theorem coefficientH_two : coefficientH 2 = 8 := by
  simp only [coefficientH, exceptionalWeight]
  norm_num
  rw [exceptionalScale_sq]
  norm_num [C,B,K,Nat.factorial]

theorem coefficientH_ge_three {d : ℕ} (hd : 3 ≤ d) :
    coefficientH d = B*K^(d-3)*(Nat.factorial d : ℝ)^2 := by
  have hd2 : d ≠ 2 := by omega
  have he : d-2 = (d-3)+1 := by omega
  simp only [coefficientH, exceptionalWeight, if_neg hd2, one_pow, mul_one]
  rw [he, pow_succ]
  dsimp [C]
  field_simp [ne_of_gt K_positive]

theorem choose_factorial_shift {ell a : ℕ} (ha : a ≤ ell) :
    (ell.choose a : ℝ)*(Nat.factorial a : ℝ)*
      (Nat.factorial (ell-a+1) : ℝ) =
      (Nat.factorial ell : ℝ)*(ell-a+1 : ℕ) := by
  have h := Nat.choose_mul_factorial_mul_factorial ha
  rw [Nat.factorial_succ]
  push_cast
  have hc : (ell.choose a : ℝ)*(Nat.factorial a : ℝ)*
      (Nat.factorial (ell-a) : ℝ) = (Nat.factorial ell : ℝ) := by
    exact_mod_cast h
  nlinarith

theorem convolution_term_identity {ell a : ℕ} (hell : 3 ≤ ell)
    (ha : a ∈ Finset.Icc 2 (ell-1)) :
    (ell.choose a : ℝ)*Real.sqrt (coefficientH a*coefficientH (ell-a+1)) =
      r*Real.sqrt (coefficientH ell)*(ell-a+1 : ℕ)*
        exceptionalWeight a*exceptionalWeight (ell-a+1) := by
  have ha2 := (Finset.mem_Icc.mp ha).1
  have hat := (Finset.mem_Icc.mp ha).2
  have hale : a ≤ ell := by omega
  have hb2 : 2 ≤ ell-a+1 := by omega
  have hl2 : ell ≠ 2 := by omega
  have hpow : K^(a-2)*K^((ell-a+1)-2)*K = K^(ell-2) := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  have hfac := choose_factorial_shift hale
  have hleft : 0 ≤ (ell.choose a : ℝ)*
      Real.sqrt (coefficientH a*coefficientH (ell-a+1)) := by positivity
  have hright : 0 ≤ r*Real.sqrt (coefficientH ell)*(ell-a+1 : ℕ)*
      exceptionalWeight a*exceptionalWeight (ell-a+1) := by
    have hr : 0 < r := by norm_num [r]
    positivity [exceptionalWeight_positive a, exceptionalWeight_positive (ell-a+1)]
  apply (sq_eq_sq₀ hleft hright).mp
  rw [mul_pow, Real.sq_sqrt
    (mul_nonneg (coefficientH_positive a).le (coefficientH_positive (ell-a+1)).le)]
  have hs : (Real.sqrt (coefficientH ell))^2 = coefficientH ell :=
    Real.sq_sqrt (coefficientH_positive ell).le
  simp only [mul_pow, hs]
  simp only [coefficientH, exceptionalWeight, if_neg hl2, one_pow, mul_one]
  change _ = _
  calc
    (ell.choose a : ℝ)^2 *
        (C*K^(a-2)*(Nat.factorial a : ℝ)^2*(if a=2 then exceptionalScale else 1)^2 *
         (C*K^((ell-a+1)-2)*(Nat.factorial (ell-a+1) : ℝ)^2*
           (if ell-a+1=2 then exceptionalScale else 1)^2)) =
        C^2*(K^(a-2)*K^((ell-a+1)-2))*
          ((ell.choose a : ℝ)*(Nat.factorial a : ℝ)*
            (Nat.factorial (ell-a+1) : ℝ))^2*
          (if a=2 then exceptionalScale else 1)^2*
          (if ell-a+1=2 then exceptionalScale else 1)^2 := by ring
    _ = C^2*(K^(a-2)*K^((ell-a+1)-2))*
          ((Nat.factorial ell : ℝ)*(ell-a+1 : ℕ))^2*
          (if a=2 then exceptionalScale else 1)^2*
          (if ell-a+1=2 then exceptionalScale else 1)^2 := by rw [hfac]
    _ = r^2*(C*K^(ell-2)*(Nat.factorial ell : ℝ)^2)*(ell-a+1 : ℕ)^2*
          (if a=2 then exceptionalScale else 1)^2*
          (if ell-a+1=2 then exceptionalScale else 1)^2 := by
      rw [← hpow, ← r_sq_mul_K]
      ring

theorem coefficientD_normalized {ell : ℕ} (hell : 3 ≤ ell) :
    coefficientD ell = r*Real.sqrt (coefficientH ell)*
      (∑ a ∈ Finset.Icc 2 (ell-1), (ell-a+1 : ℕ)*
        exceptionalWeight a*exceptionalWeight (ell-a+1)) := by
  unfold coefficientD
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [convolution_term_identity hell ha]
  ring

theorem exceptionalScale_minus_one_le_delta : exceptionalScale-1 ≤ delta := by
  have he := exceptionalScale_sq
  have hd : delta = 1/C-1/2 := by norm_num [delta,C,B,K]
  have hsq := sq_nonneg (exceptionalScale-1)
  rw [hd]
  simp only [div_eq_mul_inv] at he ⊢
  nlinarith

theorem coefficientH_succ {k : ℕ} (hk : 3 ≤ k) :
    coefficientH (k+1) = K*(k+1 : ℝ)^2*coefficientH k := by
  rw [coefficientH_ge_three (by omega), coefficientH_ge_three hk]
  rw [show k+1-3 = (k-3)+1 by omega, pow_succ, Nat.factorial_succ]
  push_cast
  ring

theorem coefficientD_bound {ell : ℕ} (hell : 3 ≤ ell) :
    coefficientD ell ≤ r*Real.sqrt (coefficientH ell)*convolutionWeight ell := by
  rw [coefficientD_normalized hell]
  have hr : 0 < r := by norm_num [r]
  have hcoef : 0 ≤ r*Real.sqrt (coefficientH ell) := by positivity
  apply mul_le_mul_of_nonneg_left _ hcoef
  have heq : exceptionalWeight = ConvolutionWeights.exceptionalWeight exceptionalScale := rfl
  rw [heq]
  by_cases h3 : ell=3
  · subst ell
    rw [ConvolutionWeights.exact_sum_three, exceptionalScale_sq]
    norm_num [convolutionWeight,delta,C,B,K]
  · rw [ConvolutionWeights.exact_sum (by omega : 4 ≤ ell)]
    unfold convolutionWeight
    have hm := mul_le_mul_of_nonneg_left exceptionalScale_minus_one_le_delta
      (show (0 : ℝ) ≤ (ell : ℝ)+1 by positivity)
    nlinarith

theorem coefficientD_div_sqrt_bound {ell : ℕ} (hell : 3 ≤ ell) :
    coefficientD ell/Real.sqrt (coefficientH ell) ≤ r*convolutionWeight ell := by
  have hs := Real.sqrt_pos.mpr (coefficientH_positive ell)
  apply (div_le_iff₀ hs).mpr
  convert coefficientD_bound hell using 1 <;> ring

theorem coefficientH_ratio {k : ℕ} (hk : 3 ≤ k) :
    coefficientH (k+1)/coefficientH k = K*(k+1 : ℝ)^2 := by
  rw [coefficientH_succ hk]
  field_simp [ne_of_gt (coefficientH_positive k)]

/-- Proposition 3.1's numerical inequality (3.22), with the actual factorial
sequence and the actual lower-degree square-root sums; no convolution or
ratio hypothesis remains in this scalar theorem. -/
theorem all_degree_scalar_criterion {k : ℕ} (hk : 3 ≤ k)
    {u : ℝ} (hu : u ∈ Set.Icc 0 1) :
    qPhi u * (alpha*coefficientH (k+1)/coefficientH k*phi u -
      (A*(k : ℝ)^2+(A-3)*k+2)*u -
      2*coefficientD k/Real.sqrt (coefficientH k)*Real.sqrt u) >
      2*(k+1 : ℝ)^2-(k+1 : ℝ)+2 +
        2*coefficientD (k+1)/Real.sqrt (coefficientH (k+1)*phi u) := by
  have hkp : 3 ≤ k+1 := by omega
  have hkreal : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hdk := coefficientD_div_sqrt_bound hk
  have hdj := coefficientD_div_sqrt_bound hkp
  have hdj' : coefficientD (k+1)/Real.sqrt (coefficientH (k+1)) ≤
      r*convolutionWeight ((k : ℝ)+1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hdj
  have hcrit := finite_rank_criterion hkreal hu hdk hdj'
  have hratio : alpha*coefficientH (k+1)/coefficientH k =
      alpha*(K*(k+1 : ℝ)^2) := by
    rw [show alpha*coefficientH (k+1)/coefficientH k =
      alpha*(coefficientH (k+1)/coefficientH k) by ring,
      coefficientH_ratio hk]
  rw [hratio, Real.sqrt_mul (coefficientH_positive (k+1)).le]
  convert hcrit using 1 <;> push_cast <;> ring

#print axioms coefficientH_ge_three
#print axioms convolution_term_identity
#print axioms coefficientD_normalized
#print axioms coefficientD_bound
#print axioms all_degree_scalar_criterion
end Quintic24886

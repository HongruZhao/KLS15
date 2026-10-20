import QuinticConvolution

/-! Generic positive factorial/geometric coefficient data. Exact lower
convolution normalization is proved for arbitrary B,K and their true r. -/
noncomputable section
open scoped BigOperators
namespace KLS.DeterministicBridgeNext

structure FactorialScheme where
  B : ℝ
  K : ℝ
  r : ℝ
  B_positive : 0<B
  K_positive : 0<K
  r_positive : 0<r
  r_sq_mul_K : r^2*K=B/K

namespace FactorialScheme

def C (s : FactorialScheme) : ℝ := s.B/s.K
def exceptionalScale (s : FactorialScheme) : ℝ := Real.sqrt (2/s.C)
def exceptionalWeight (s : FactorialScheme) (d : ℕ) : ℝ := if d=2 then s.exceptionalScale else 1
def coefficientH (s : FactorialScheme) (d : ℕ) : ℝ :=
  s.C*s.K^(d-2)*(Nat.factorial d : ℝ)^2*(s.exceptionalWeight d)^2
def coefficientD (s : FactorialScheme) (ell : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 2 (ell-1),
    (ell.choose a : ℝ)*Real.sqrt (s.coefficientH a*s.coefficientH (ell-a+1))
def delta (s : FactorialScheme) : ℝ := 1/s.C-1/2
def convolutionWeight (s : FactorialScheme) (k : ℝ) : ℝ := k*(k-1)/2-1+s.delta*(k+1)

variable {s : FactorialScheme}
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem C_positive : 0 < s.C := div_pos s.B_positive s.K_positive
theorem exceptionalScale_positive : 0 < s.exceptionalScale := by
  exact Real.sqrt_pos.mpr (div_pos (by norm_num) (C_positive (s := s)))
theorem exceptionalScale_sq : s.exceptionalScale^2 = 2/s.C :=
  Real.sq_sqrt (by positivity [C_positive (s := s)])
theorem exceptionalWeight_positive (d : ℕ) : 0 < s.exceptionalWeight d := by
  unfold FactorialScheme.exceptionalWeight
  split_ifs <;> first | exact exceptionalScale_positive (s := s) | norm_num
theorem coefficientH_positive (d : ℕ) : 0 < s.coefficientH d := by
  unfold FactorialScheme.coefficientH
  positivity [C_positive (s := s), s.K_positive, exceptionalWeight_positive (s := s) d]
theorem r_sq_mul_K_eq_C : s.r^2*s.K=s.C := s.r_sq_mul_K

theorem coefficientH_two : s.coefficientH 2 = 8 := by
  simp only [FactorialScheme.coefficientH, FactorialScheme.exceptionalWeight]
  norm_num
  rw [exceptionalScale_sq (s := s)]
  field_simp [ne_of_gt (C_positive (s := s))]
  ring

theorem coefficientH_ge_three {d : ℕ} (hd : 3 ≤ d) :
    s.coefficientH d = s.B*s.K^(d-3)*(Nat.factorial d : ℝ)^2 := by
  have hd2 : d ≠ 2 := by omega
  have he : d-2 = (d-3)+1 := by omega
  simp only [FactorialScheme.coefficientH, FactorialScheme.exceptionalWeight, if_neg hd2, one_pow, mul_one]
  rw [he, pow_succ]
  dsimp [FactorialScheme.C]
  field_simp [ne_of_gt s.K_positive]

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
    (ell.choose a : ℝ)*Real.sqrt (s.coefficientH a*s.coefficientH (ell-a+1)) =
      s.r*Real.sqrt (s.coefficientH ell)*(ell-a+1 : ℕ)*
        s.exceptionalWeight a*s.exceptionalWeight (ell-a+1) := by
  have ha2 := (Finset.mem_Icc.mp ha).1
  have hat := (Finset.mem_Icc.mp ha).2
  have hale : a ≤ ell := by omega
  have hb2 : 2 ≤ ell-a+1 := by omega
  have hl2 : ell ≠ 2 := by omega
  have hpow : s.K^(a-2)*s.K^((ell-a+1)-2)*s.K = s.K^(ell-2) := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  have hfac := choose_factorial_shift hale
  have hleft : 0 ≤ (ell.choose a : ℝ)*
      Real.sqrt (s.coefficientH a*s.coefficientH (ell-a+1)) := by positivity
  have hright : 0 ≤ s.r*Real.sqrt (s.coefficientH ell)*(ell-a+1 : ℕ)*
      s.exceptionalWeight a*s.exceptionalWeight (ell-a+1) := by
    have hr : 0 < s.r := s.r_positive
    positivity [exceptionalWeight_positive (s := s) a, exceptionalWeight_positive (s := s) (ell-a+1)]
  apply (sq_eq_sq₀ hleft hright).mp
  rw [mul_pow, Real.sq_sqrt
    (mul_nonneg (coefficientH_positive (s := s) a).le (coefficientH_positive (s := s) (ell-a+1)).le)]
  have hs : (Real.sqrt (s.coefficientH ell))^2 = s.coefficientH ell :=
    Real.sq_sqrt (coefficientH_positive (s := s) ell).le
  simp only [mul_pow, hs]
  simp only [FactorialScheme.coefficientH, FactorialScheme.exceptionalWeight, if_neg hl2, one_pow, mul_one]
  change _ = _
  calc
    (ell.choose a : ℝ)^2 *
        (s.C*s.K^(a-2)*(Nat.factorial a : ℝ)^2*(if a=2 then s.exceptionalScale else 1)^2 *
         (s.C*s.K^((ell-a+1)-2)*(Nat.factorial (ell-a+1) : ℝ)^2*
           (if ell-a+1=2 then s.exceptionalScale else 1)^2)) =
        s.C^2*(s.K^(a-2)*s.K^((ell-a+1)-2))*
          ((ell.choose a : ℝ)*(Nat.factorial a : ℝ)*
            (Nat.factorial (ell-a+1) : ℝ))^2*
          (if a=2 then s.exceptionalScale else 1)^2*
          (if ell-a+1=2 then s.exceptionalScale else 1)^2 := by ring
    _ = s.C^2*(s.K^(a-2)*s.K^((ell-a+1)-2))*
          ((Nat.factorial ell : ℝ)*(ell-a+1 : ℕ))^2*
          (if a=2 then s.exceptionalScale else 1)^2*
          (if ell-a+1=2 then s.exceptionalScale else 1)^2 := by rw [hfac]
    _ = s.r^2*(s.C*s.K^(ell-2)*(Nat.factorial ell : ℝ)^2)*(ell-a+1 : ℕ)^2*
          (if a=2 then s.exceptionalScale else 1)^2*
          (if ell-a+1=2 then s.exceptionalScale else 1)^2 := by
      rw [← hpow, ← r_sq_mul_K_eq_C (s := s)]
      ring

theorem coefficientD_normalized {ell : ℕ} (hell : 3 ≤ ell) :
    s.coefficientD ell = s.r*Real.sqrt (s.coefficientH ell)*
      (∑ a ∈ Finset.Icc 2 (ell-1), (ell-a+1 : ℕ)*
        s.exceptionalWeight a*s.exceptionalWeight (ell-a+1)) := by
  unfold FactorialScheme.coefficientD
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [convolution_term_identity (s := s) hell ha]
  ring

theorem exceptionalScale_minus_one_le_delta : s.exceptionalScale-1 ≤ s.delta := by
  have he := exceptionalScale_sq (s := s)
  have hd : s.delta = 1/s.C-1/2 := rfl
  have hsq := sq_nonneg (s.exceptionalScale-1)
  rw [hd]
  simp only [div_eq_mul_inv] at he ⊢
  nlinarith

theorem coefficientH_succ {k : ℕ} (hk : 3 ≤ k) :
    s.coefficientH (k+1) = s.K*(k+1 : ℝ)^2*s.coefficientH k := by
  rw [coefficientH_ge_three (s := s) (by omega), coefficientH_ge_three (s := s) hk]
  rw [show k+1-3 = (k-3)+1 by omega, pow_succ, Nat.factorial_succ]
  push_cast
  ring

theorem coefficientD_bound {ell : ℕ} (hell : 3 ≤ ell) :
    s.coefficientD ell ≤ s.r*Real.sqrt (s.coefficientH ell)*s.convolutionWeight ell := by
  rw [coefficientD_normalized (s := s) hell]
  have hr : 0 < s.r := s.r_positive
  have hcoef : 0 ≤ s.r*Real.sqrt (s.coefficientH ell) := by positivity
  apply mul_le_mul_of_nonneg_left _ hcoef
  have heq : s.exceptionalWeight = ConvolutionWeights.exceptionalWeight s.exceptionalScale := rfl
  rw [heq]
  by_cases h3 : ell=3
  · subst ell
    rw [ConvolutionWeights.exact_sum_three, exceptionalScale_sq (s := s)]
    dsimp [FactorialScheme.convolutionWeight,FactorialScheme.delta]
    ring_nf <;> exact le_rfl
  · rw [ConvolutionWeights.exact_sum (by omega : 4 ≤ ell)]
    unfold FactorialScheme.convolutionWeight
    have hm := mul_le_mul_of_nonneg_left (exceptionalScale_minus_one_le_delta (s := s))
      (show (0 : ℝ) ≤ (ell : ℝ)+1 by positivity)
    nlinarith

theorem coefficientD_div_sqrt_bound {ell : ℕ} (hell : 3 ≤ ell) :
    s.coefficientD ell/Real.sqrt (s.coefficientH ell) ≤ s.r*s.convolutionWeight ell := by
  have hs := Real.sqrt_pos.mpr (coefficientH_positive (s := s) ell)
  apply (div_le_iff₀ hs).mpr
  convert coefficientD_bound (s := s) hell using 1 <;> ring

theorem coefficientH_ratio {k : ℕ} (hk : 3 ≤ k) :
    s.coefficientH (k+1)/s.coefficientH k = s.K*(k+1 : ℝ)^2 := by
  rw [coefficientH_succ (s := s) hk]
  field_simp [ne_of_gt (coefficientH_positive (s := s) k)]



theorem coefficientH_one : s.coefficientH 1 = s.C := by
  norm_num [coefficientH, exceptionalWeight]

def of_pos (B K : ℝ) (hB : 0<B) (hK : 0<K) : FactorialScheme where
  B := B
  K := K
  r := Real.sqrt B/K
  B_positive := hB
  K_positive := hK
  r_positive := div_pos (Real.sqrt_pos.mpr hB) hK
  r_sq_mul_K := by
    rw [div_pow,Real.sq_sqrt hB.le]
    field_simp

@[simp] theorem of_pos_B (B K : ℝ) (hB : 0<B) (hK : 0<K) :
    (of_pos B K hB hK).B=B := rfl
@[simp] theorem of_pos_K (B K : ℝ) (hB : 0<B) (hK : 0<K) :
    (of_pos B K hB hK).K=K := rfl


end FactorialScheme
end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.FactorialScheme.coefficientH_two
#print axioms KLS.DeterministicBridgeNext.FactorialScheme.convolution_term_identity
#print axioms KLS.DeterministicBridgeNext.FactorialScheme.coefficientD_bound

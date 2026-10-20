import KLSConstantImprovement.ExponentialPolynomialSign

/-! Exact derivatives and initial jets of finite exponential polynomials.
These formulas supply the analytic identification for rational hinge data.
They make no assertion about a log-concave law or universal curvature. -/
noncomputable section
open scoped BigOperators ContDiff
namespace KLSConstantImprovement.ExponentialPolynomialDerivatives
set_option maxHeartbeats 2000000

abbrev Monomial := ℕ×ℝ×ℝ
def monomial (t : Monomial) (L : ℝ) : ℝ :=
  t.2.2*L^t.1*Real.exp (t.2.1*L)
def polynomial (ts : List Monomial) (L : ℝ) : ℝ :=
  (ts.map fun t=>monomial t L).sum

theorem monomial_contDiff (t : Monomial) (n : ℕ∞ω) :
    ContDiff ℝ n (monomial t) := by
  unfold monomial
  fun_prop

theorem polynomial_contDiff (ts : List Monomial) (n : ℕ∞ω) :
    ContDiff ℝ n (polynomial ts) := by
  induction ts with
  | nil =>
    change ContDiff ℝ n (fun _ : ℝ => (0 : ℝ))
    exact contDiff_const
  | cons t ts ih =>
    have hfun : polynomial (t::ts)=fun L=>monomial t L+polynomial ts L := rfl
    rw [hfun]
    exact (monomial_contDiff t n).add ih

theorem monomial_iteratedDeriv (t : Monomial) (n : ℕ) (L : ℝ) :
    iteratedDeriv n (monomial t) L =
      t.2.2 * ∑ i ∈ Finset.range (n+1),
        (n.choose i : ℝ)*(t.1.descFactorial i : ℝ)*L^(t.1-i)*
          t.2.1^(n-i)*Real.exp (t.2.1*L) := by
  unfold monomial
  rw [show (fun L=>t.2.2*L^t.1*Real.exp (t.2.1*L))=
      (fun L=>t.2.2*(L^t.1*Real.exp (t.2.1*L))) by funext L;ring]
  rw [iteratedDeriv_const_mul_field]
  rw [iteratedDeriv_fun_mul (by fun_prop) (by fun_prop)]
  simp only [iteratedDeriv_pow,iteratedDeriv_exp_const_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem monomial_initial_derivative (t : Monomial) (n : ℕ) :
    iteratedDeriv n (monomial t) 0 =
      if t.1 ≤ n then t.2.2*(n.descFactorial t.1 : ℝ)*t.2.1^(n-t.1) else 0 := by
  unfold monomial
  rw [show (fun L=>t.2.2*L^t.1*Real.exp (t.2.1*L))=
      (fun L=>t.2.2*(L^t.1*Real.exp (t.2.1*L))) by funext L;ring]
  rw [iteratedDeriv_const_mul_field]
  rw [iteratedDeriv_fun_mul (by fun_prop) (by fun_prop)]
  simp only [iteratedDeriv_fun_pow_zero,iteratedDeriv_exp_const_mul,
    mul_zero,Real.exp_zero,mul_one]
  simp only [Nat.cast_ite,Nat.cast_zero,mul_ite,ite_mul,mul_zero,zero_mul]
  rw [Finset.sum_ite_eq']
  by_cases h:t.1 ≤ n
  · simp only [Finset.mem_range,Nat.lt_succ_iff,h,if_true]
    rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]
    ring
  · simp only [Finset.mem_range,Nat.lt_succ_iff,h,if_false,mul_zero]

theorem polynomial_iteratedDeriv (ts : List Monomial) (n : ℕ) (L : ℝ) :
    iteratedDeriv n (polynomial ts) L=
      (ts.map fun t=>iteratedDeriv n (monomial t) L).sum := by
  induction ts with
  | nil =>
    change iteratedDeriv n (fun _ : ℝ=>0) L=0
    simp [iteratedDeriv_const]
  | cons t ts ih =>
    have hfun : polynomial (t::ts)=fun L=>monomial t L+polynomial ts L := rfl
    rw [hfun,iteratedDeriv_fun_add (monomial_contDiff t n).contDiffAt
      (polynomial_contDiff ts n).contDiffAt,ih]
    rfl

theorem polynomial_derivative_chain (ts : List Monomial) (n : ℕ) (L : ℝ) :
    HasDerivAt (iteratedDeriv n (polynomial ts))
      (iteratedDeriv (n+1) (polynomial ts) L) L := by
  rw [iteratedDeriv_succ]
  exact ((polynomial_contDiff ts (n+1)).differentiable_iteratedDeriv' n L).hasDerivAt

end KLSConstantImprovement.ExponentialPolynomialDerivatives
#print axioms KLSConstantImprovement.ExponentialPolynomialDerivatives.monomial_iteratedDeriv
#print axioms KLSConstantImprovement.ExponentialPolynomialDerivatives.monomial_initial_derivative
#print axioms KLSConstantImprovement.ExponentialPolynomialDerivatives.polynomial_iteratedDeriv
#print axioms KLSConstantImprovement.ExponentialPolynomialDerivatives.polynomial_derivative_chain

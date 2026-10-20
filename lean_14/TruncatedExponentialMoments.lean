import Mathlib

/-! Actual truncated exponential integrals, including their moment recursion.
No moment values are supplied as hypotheses. -/
noncomputable section
open MeasureTheory Set
namespace KLSImprovement.TruncatedExponential
set_option maxHeartbeats 1000000

def moment (b : ℝ) (k : ℕ) : ℝ :=
  ∫ x in (0:ℝ)..1, x^k*Real.exp (-b*x)

def value (b w : ℝ) : ℕ → ℝ
  | 0 => (1-w)/b
  | k+1 => ((k+1:ℕ)*value b w k-w)/b

theorem integrable (b : ℝ) (k : ℕ) :
    IntervalIntegrable (fun x : ℝ => x^k*Real.exp (-b*x)) volume 0 1 := by
  exact (by fun_prop : Continuous (fun x : ℝ => x^k*Real.exp (-b*x))).intervalIntegrable _ _

theorem exp_derivative (b x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-b*y))
      ((-b)*Real.exp (-b*x)) x := by
  simpa [Function.comp_def,mul_comm] using
    (Real.hasDerivAt_exp (-b*x)).comp x ((hasDerivAt_id x).const_mul (-b))

theorem moment_zero (b : ℝ) (hb : b ≠ 0) :
    moment b 0=(1-Real.exp (-b))/b := by
  have hi : IntervalIntegrable (fun x : ℝ => (-b)*Real.exp (-b*x)) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ => (-b)*Real.exp (-b*x))).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => exp_derivative b x) hi
  rw [intervalIntegral.integral_const_mul] at h
  simp only [mul_one,mul_zero,Real.exp_zero] at h
  dsimp [moment]
  simp only [pow_zero,one_mul]
  apply (eq_div_iff hb).2
  nlinarith

theorem moment_succ (b : ℝ) (hb : b ≠ 0) (k : ℕ) :
    moment b (k+1)=((k+1:ℕ)*moment b k-Real.exp (-b))/b := by
  have hu : ContinuousOn (fun x : ℝ => x^(k+1)) (uIcc 0 1) := by fun_prop
  have hv : ContinuousOn (fun x : ℝ => Real.exp (-b*x)) (uIcc 0 1) := by fun_prop
  have hdu : ∀ x ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1),
      HasDerivAt (fun y : ℝ => y^(k+1)) ((k+1:ℕ)*x^k) x := by
    intro x _
    simpa only [Nat.add_sub_cancel] using hasDerivAt_pow (k+1) x
  have hdv : ∀ x ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1),
      HasDerivAt (fun y : ℝ => Real.exp (-b*y)) ((-b)*Real.exp (-b*x)) x := by
    intro x _
    exact exp_derivative b x
  have hdui : IntervalIntegrable (fun x : ℝ => (k+1:ℕ)*x^k) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ => (k+1:ℕ)*x^k)).intervalIntegrable _ _
  have hdvi : IntervalIntegrable (fun x : ℝ => (-b)*Real.exp (-b*x)) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ => (-b)*Real.exp (-b*x))).intervalIntegrable _ _
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hu hv hdu hdv hdui hdvi
  have he : (fun x : ℝ => x^(k+1)*((-b)*Real.exp (-b*x)))=
      (fun x : ℝ => (-b)*(x^(k+1)*Real.exp (-b*x))) := by funext x; ring
  have he' : (fun x : ℝ => ((k+1:ℕ)*x^k)*Real.exp (-b*x))=
      (fun x : ℝ => (k+1:ℕ)*(x^k*Real.exp (-b*x))) := by funext x; ring
  rw [he,he',intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h
  simp only [one_pow,mul_one,one_mul,mul_zero,Real.exp_zero,
    zero_pow (Nat.succ_ne_zero k),sub_zero] at h
  change (-b)*moment b (k+1)=Real.exp (-b)-(k+1:ℕ)*moment b k at h
  apply (eq_div_iff hb).2
  nlinarith

theorem moment_eq_value (b : ℝ) (hb : b ≠ 0) (k : ℕ) :
    moment b k=value b (Real.exp (-b)) k := by
  induction k with
  | zero => exact moment_zero b hb
  | succ k ih => rw [moment_succ b hb k,ih,value]

theorem moment_at_zero (k : ℕ) : moment 0 k=1/(k+1:ℕ) := by
  simp only [moment,neg_zero,zero_mul,Real.exp_zero,mul_one]
  rw [integral_pow]
  simp

end KLSImprovement.TruncatedExponential
#print axioms KLSImprovement.TruncatedExponential.moment_zero
#print axioms KLSImprovement.TruncatedExponential.moment_succ
#print axioms KLSImprovement.TruncatedExponential.moment_eq_value
#print axioms KLSImprovement.TruncatedExponential.moment_at_zero

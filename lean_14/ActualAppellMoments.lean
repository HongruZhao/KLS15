import ExponentialMoments

/-!
# All-order scalar exponential polynomial moments

For the actual rate-one exponential law, the Appell polynomial of positive
degree `m+1`, expressed in the uncentered coordinate Y, is
`Y^(m+1)-(m+1)Y^m`. This file proves its centering and exact normalized square
integral for every m. The identification with KLS15's normalized tilt derivative
definition is not assumed or formalized here.
-/

open MeasureTheory ProbabilityTheory
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace KLSImprovement.Exponential

open KLSImprovement.ExponentialMoments
local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

def appell (m : ℕ) (y : ℝ) : ℝ := y ^ (m + 1) - ((m : ℝ) + 1) * y ^ m

theorem integrable_appell (m : ℕ) : Integrable (appell m) (expMeasure 1) := by
  exact (expMeasure_one_nat_moment (m + 1)).1.sub
    ((expMeasure_one_nat_moment m).1.const_mul ((m : ℝ) + 1))

theorem integral_appell (m : ℕ) : (∫ y, appell m y ∂expMeasure 1) = 0 := by
  simp only [appell]
  rw [integral_sub (expMeasure_one_nat_moment (m + 1)).1
    ((expMeasure_one_nat_moment m).1.const_mul ((m : ℝ) + 1)),
    integral_const_mul, (expMeasure_one_nat_moment (m + 1)).2,
    (expMeasure_one_nat_moment m).2, Nat.factorial_succ]
  push_cast
  ring

theorem appell_square_expansion (m : ℕ) :
    (fun y : ℝ => (appell m y) ^ 2) =
      (fun y : ℝ => y ^ (2 * m + 2) - 2 * ((m : ℝ) + 1) * y ^ (2 * m + 1) +
        ((m : ℝ) + 1) ^ 2 * y ^ (2 * m)) := by
  funext y
  have hm : 2 * m = m * 2 := by omega
  simp only [appell, hm, pow_add, pow_mul, pow_one]
  ring

theorem integrable_appell_sq (m : ℕ) :
    Integrable (fun y => (appell m y) ^ 2) (expMeasure 1) := by
  rw [appell_square_expansion]
  exact ((expMeasure_one_nat_moment (2 * m + 2)).1.sub
    ((expMeasure_one_nat_moment (2 * m + 1)).1.const_mul (2 * ((m : ℝ) + 1)))).add
    ((expMeasure_one_nat_moment (2 * m)).1.const_mul (((m : ℝ) + 1) ^ 2))

theorem integral_appell_sq (m : ℕ) :
    (∫ y, (appell m y) ^ 2 ∂expMeasure 1) =
      ((m : ℝ) + 1) ^ 2 * ((2 * m).factorial : ℝ) := by
  rw [appell_square_expansion]
  have h₁ := (expMeasure_one_nat_moment (2 * m + 2)).1
  have h₂ := (expMeasure_one_nat_moment (2 * m + 1)).1
  have h₃ := (expMeasure_one_nat_moment (2 * m)).1
  have hsub : Integrable (fun y : ℝ => y ^ (2 * m + 2) -
      2 * ((m : ℝ) + 1) * y ^ (2 * m + 1)) (expMeasure 1) := by
    convert h₁.sub (h₂.const_mul (2 * ((m : ℝ) + 1))) using 1
  rw [integral_add (f := fun y : ℝ => y ^ (2 * m + 2) -
    2 * ((m : ℝ) + 1) * y ^ (2 * m + 1))
    (g := fun y : ℝ => ((m : ℝ) + 1) ^ 2 * y ^ (2 * m))
    hsub (h₃.const_mul (((m : ℝ) + 1) ^ 2)),
    integral_sub (f := fun y : ℝ => y ^ (2 * m + 2))
      (g := fun y : ℝ => 2 * ((m : ℝ) + 1) * y ^ (2 * m + 1))
      h₁ (h₂.const_mul (2 * ((m : ℝ) + 1))),
    integral_const_mul, integral_const_mul,
    (expMeasure_one_nat_moment (2 * m + 2)).2,
    (expMeasure_one_nat_moment (2 * m + 1)).2,
    (expMeasure_one_nat_moment (2 * m)).2]
  rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega,
    Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  ring

/-- The exact scalar normalized Appell square integral is the central binomial
coefficient. It is an actual measure integral for every degree, not a numerical
cap supplied as a hypothesis. -/
theorem normalized_integral_appell_sq (m : ℕ) :
    (∫ y, (appell m y) ^ 2 ∂expMeasure 1) /
      ((m + 1).factorial : ℝ) ^ 2 = ((2 * m).choose m : ℝ) := by
  rw [integral_appell_sq, Nat.factorial_succ]
  have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  have hchoose : ((2 * m).choose m : ℝ) * (m.factorial : ℝ) *
      (m.factorial : ℝ) = ((2 * m).factorial : ℝ) := by
    have he := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
    rw [show 2 * m - m = m by omega] at he
    exact_mod_cast he
  push_cast
  field_simp [hf, hm]
  nlinarith [hchoose]

end KLSImprovement.Exponential

#print axioms KLSImprovement.Exponential.integral_appell
#print axioms KLSImprovement.Exponential.integral_appell_sq
#print axioms KLSImprovement.Exponential.normalized_integral_appell_sq

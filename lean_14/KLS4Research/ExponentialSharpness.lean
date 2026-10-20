import ExponentialMoments
import KLS.RouteArithmetic

/-! Actual scalar exponential witnesses for the sharp lower bound four.
This file starts with the concrete measure. The original Euclidean KLS
interface is developed separately below; scalar algebra alone is insufficient.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace KLS4Research.ExponentialSharpness
open KLSImprovement.ExponentialMoments

local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

def scalarTrial (a y : ℝ) : ℝ := Real.exp (a * y)

theorem scalarTrial_memLp (a : ℝ) (ha : a < 1 / 2) :
    MemLp (scalarTrial a) 2 (expMeasure 1) := by
  apply (memLp_two_iff_integrable_sq (by unfold scalarTrial; fun_prop)).mpr
  have he : (fun y => scalarTrial a y ^ 2) =
      (fun y : ℝ => Real.exp ((2 * a) * y)) := by
    funext y
    simp only [scalarTrial, pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact (expMeasure_one_exponential_moment (2 * a) (by linarith)).1

theorem scalarTrial_integral (a : ℝ) (ha : a < 1) :
    (∫ y, scalarTrial a y ∂expMeasure 1) = 1 / (1 - a) :=
  (expMeasure_one_exponential_moment a ha).2

theorem scalarTrial_integral_sq (a : ℝ) (ha : a < 1 / 2) :
    (∫ y, scalarTrial a y ^ 2 ∂expMeasure 1) = 1 / (1 - 2 * a) := by
  have he : (fun y => scalarTrial a y ^ 2) =
      (fun y : ℝ => Real.exp ((2 * a) * y)) := by
    funext y
    simp only [scalarTrial, pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact (expMeasure_one_exponential_moment (2 * a) (by linarith)).2

theorem scalarTrial_variance (a : ℝ) (ha : a < 1 / 2) :
    ProbabilityTheory.variance (scalarTrial a) (expMeasure 1) =
      1 / (1 - 2 * a) - (1 / (1 - a)) ^ 2 := by
  rw [ProbabilityTheory.variance_eq_sub (scalarTrial_memLp a ha)]
  change (∫ y, scalarTrial a y ^ 2 ∂expMeasure 1) -
    (∫ y, scalarTrial a y ∂expMeasure 1) ^ 2 = _
  rw [scalarTrial_integral_sq a ha, scalarTrial_integral a (by linarith)]

theorem scalarTrial_deriv (a y : ℝ) :
    deriv (scalarTrial a) y = a * scalarTrial a y := by
  have h := ((hasDerivAt_id y).const_mul a).exp
  change deriv (fun y : ℝ => Real.exp (a * y)) y = a * Real.exp (a * y)
  simpa [mul_comm] using h.deriv

theorem scalarTrial_energy (a : ℝ) (ha : a < 1 / 2) :
    (∫ y, deriv (scalarTrial a) y ^ 2 ∂expMeasure 1) =
      a ^ 2 / (1 - 2 * a) := by
  simp_rw [scalarTrial_deriv, mul_pow]
  rw [integral_const_mul, scalarTrial_integral_sq a ha]
  ring

theorem scalarTrial_quotient (a : ℝ) (ha : 0 < a) (ha2 : a < 1 / 2) :
    ProbabilityTheory.variance (scalarTrial a) (expMeasure 1) /
      (∫ y, deriv (scalarTrial a) y ^ 2 ∂expMeasure 1) =
        1 / (1 - a) ^ 2 := by
  rw [scalarTrial_variance a ha2, scalarTrial_energy a ha2]
  exact KLS.RouteArithmetic.exponential_moment_ratio_algebra a ha ha2

theorem four_le_scalar_constant (C : ℝ)
    (hC : ∀ a : ℝ, 0 < a → a < 1 / 2 →
      ProbabilityTheory.variance (scalarTrial a) (expMeasure 1) ≤
        C * (∫ y, deriv (scalarTrial a) y ^ 2 ∂expMeasure 1)) :
    4 ≤ C := by
  apply KLS.RouteArithmetic.four_le_of_scalar_ratio_bounds C
  intro a ha ha2
  rw [← scalarTrial_quotient a ha ha2]
  apply (div_le_iff₀ ?_).mpr (hC a ha ha2)
  rw [scalarTrial_energy a ha2]
  exact KLS.RouteArithmetic.exponential_energy_expression_pos a ha ha2

end KLS4Research.ExponentialSharpness
#print axioms KLS4Research.ExponentialSharpness.scalarTrial_quotient
#print axioms KLS4Research.ExponentialSharpness.four_le_scalar_constant

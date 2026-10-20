import Mathlib

/-!
# Actual moments of the standard exponential measure

Adapted without changing the analytic proof from KLS500/KLS/ExponentialMoments.lean.
The original source is preserved. This separate namespace imports Mathlib only.

The measure in every theorem below is mathlib's `ProbabilityTheory.expMeasure 1`.
Integrability is established before each use of a real variance formula.
These are analytic facts about a concrete probability measure, not assumed
moment values. No log-concavity or KLS theorem is used or asserted.
-/

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Set Filter

noncomputable section
set_option maxHeartbeats 1200000
namespace KLSImprovement.ExponentialMoments

local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

private theorem measurable_exponentialPDF_one : Measurable (exponentialPDF 1) := by
  unfold exponentialPDF
  fun_prop

private theorem exponentialPDF_one_lt_top :
    ∀ᵐ y : ℝ ∂volume, exponentialPDF 1 y < ⊤ :=
  Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

private theorem exponentialPDF_one_smul_eq_indicator (f : ℝ → ℝ) :
    (fun y => (exponentialPDF 1 y).toReal • f y) =
      (Ici (0 : ℝ)).indicator (fun y => Real.exp (-y) * f y) := by
  funext y
  by_cases hy : 0 ≤ y
  · simp [exponentialPDF_eq, hy, smul_eq_mul, (Real.exp_pos (-y)).le]
  · simp [exponentialPDF_eq, hy, smul_eq_mul]

/-- Integrability under the actual exponential law reduces to the weighted
Lebesgue integral on its half-line support. -/
theorem integrable_expMeasure_one_iff (f : ℝ → ℝ) :
    Integrable f (expMeasure 1) ↔
      IntegrableOn (fun y => Real.exp (-y) * f y) (Ici (0 : ℝ)) := by
  change Integrable f (volume.withDensity (exponentialPDF 1)) ↔ _
  rw [integrable_withDensity_iff_integrable_smul'
    measurable_exponentialPDF_one exponentialPDF_one_lt_top]
  rw [exponentialPDF_one_smul_eq_indicator, integrable_indicator_iff measurableSet_Ici]

/-- The density formula for the actual exponential measure. This equality
alone is not used to infer integrability of either side. -/
theorem integral_expMeasure_one (f : ℝ → ℝ) :
    (∫ y : ℝ, f y ∂expMeasure 1) =
      ∫ y : ℝ in Ici 0, Real.exp (-y) * f y := by
  change (∫ y : ℝ, f y ∂volume.withDensity (exponentialPDF 1)) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    measurable_exponentialPDF_one exponentialPDF_one_lt_top,
    exponentialPDF_one_smul_eq_indicator, integral_indicator measurableSet_Ici]

/-- Every exponential moment below the rate is integrable and has the usual
value, proved for mathlib's actual probability measure. -/
theorem expMeasure_one_exponential_moment (a : ℝ) (ha : a < 1) :
    Integrable (fun y : ℝ => Real.exp (a * y)) (expMeasure 1) ∧
    (∫ y : ℝ, Real.exp (a * y) ∂expMeasure 1) = 1 / (1 - a) := by
  have hexp : (fun y : ℝ => Real.exp (-y) * Real.exp (a * y)) =
      (fun y : ℝ => Real.exp ((a - 1) * y)) := by
    funext y
    rw [← Real.exp_add]
    congr 1
    ring
  have hneg : a - 1 < 0 := by linarith
  constructor
  · rw [integrable_expMeasure_one_iff, hexp,
      integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_exp_mul_Ioi hneg 0
  · rw [integral_expMeasure_one, hexp, integral_Ici_eq_integral_Ioi,
      integral_exp_mul_Ioi hneg]
    simp only [mul_zero, Real.exp_zero]
    have hne : 1 - a ≠ 0 := by linarith
    have hne' : a - 1 ≠ 0 := by linarith
    field_simp [hne, hne']
    ring

/-- All natural moments are integrable, with value `k!`. -/
theorem expMeasure_one_nat_moment (k : ℕ) :
    Integrable (fun y : ℝ => y ^ k) (expMeasure 1) ∧
    (∫ y : ℝ, y ^ k ∂expMeasure 1) = (k.factorial : ℝ) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  constructor
  · rw [integrable_expMeasure_one_iff, integrableOn_Ici_iff_integrableOn_Ioi]
    simpa using (Real.GammaIntegral_convergent hk)
  · rw [integral_expMeasure_one, integral_Ici_eq_integral_Ioi]
    simpa [mul_comm, Real.Gamma_nat_eq_factorial] using
      (Real.integral_rpow_mul_exp_neg_mul_Ioi hk (by norm_num : (0 : ℝ) < 1))

theorem expMeasure_one_integrable_id : Integrable (fun y : ℝ => y) (expMeasure 1) := by
  simpa using (expMeasure_one_nat_moment 1).1

theorem expMeasure_one_integral_id : (∫ y : ℝ, y ∂expMeasure 1) = 1 := by
  simpa using (expMeasure_one_nat_moment 1).2

theorem expMeasure_one_integral_sq : (∫ y : ℝ, y ^ 2 ∂expMeasure 1) = 2 := by
  simpa using (expMeasure_one_nat_moment 2).2

theorem expMeasure_one_memLp_id : MemLp (fun y : ℝ => y) 2 (expMeasure 1) :=
  (memLp_two_iff_integrable_sq (by fun_prop)).mpr (expMeasure_one_nat_moment 2).1

theorem expMeasure_one_integral_centered : (∫ y : ℝ, y - 1 ∂expMeasure 1) = 0 := by
  rw [integral_sub expMeasure_one_integrable_id (integrable_const 1),
    expMeasure_one_integral_id]
  simp

theorem expMeasure_one_memLp_centered :
    MemLp (fun y : ℝ => y - 1) 2 (expMeasure 1) :=
  expMeasure_one_memLp_id.sub (memLp_const 1)

theorem expMeasure_one_variance_id :
    ProbabilityTheory.variance (fun y : ℝ => y) (expMeasure 1) = 1 := by
  rw [ProbabilityTheory.variance_eq_sub expMeasure_one_memLp_id]
  change (∫ y : ℝ, y ^ 2 ∂expMeasure 1) -
    (∫ y : ℝ, y ∂expMeasure 1) ^ 2 = 1
  rw [expMeasure_one_integral_sq, expMeasure_one_integral_id]
  norm_num

theorem expMeasure_one_variance_centered :
    ProbabilityTheory.variance (fun y : ℝ => y - 1) (expMeasure 1) = 1 := by
  rw [ProbabilityTheory.variance_sub_const (by fun_prop)]
  exact expMeasure_one_variance_id

theorem expMeasure_one_evariance_centered :
    ProbabilityTheory.evariance (fun y : ℝ => y - 1) (expMeasure 1) = 1 := by
  rw [← ProbabilityTheory.ofReal_variance expMeasure_one_memLp_centered,
    expMeasure_one_variance_centered]
  norm_num

/-- The centered third moment is proved from the actual exponential density,
not supplied as a cumulant assumption. -/
theorem expMeasure_one_integrable_centered_cube :
    Integrable (fun y : ℝ => (y - 1) ^ 3) (expMeasure 1) := by
  have h3 := (expMeasure_one_nat_moment 3).1
  have h2 := (expMeasure_one_nat_moment 2).1
  have h1 := expMeasure_one_integrable_id
  have h23 : Integrable (fun y : ℝ => y ^ 3 - 3 * y ^ 2) (expMeasure 1) := by
    convert h3.sub (h2.const_mul (3 : ℝ)) using 1
  have h1s : Integrable (fun y : ℝ => 3 * y) (expMeasure 1) := h1.const_mul (3 : ℝ)
  have h123 : Integrable (fun y : ℝ => (y ^ 3 - 3 * y ^ 2) + 3 * y)
      (expMeasure 1) := by
    convert h23.add h1s using 1
  convert h123.sub
    (integrable_const 1) using 1
  funext y
  simp only [Pi.sub_apply]
  ring

theorem expMeasure_one_integral_centered_cube :
    (∫ y : ℝ, (y - 1) ^ 3 ∂expMeasure 1) = 2 := by
  have h3 := (expMeasure_one_nat_moment 3).1
  have h2 := (expMeasure_one_nat_moment 2).1
  have h1 := expMeasure_one_integrable_id
  have h23 : Integrable (fun y : ℝ => y ^ 3 - 3 * y ^ 2) (expMeasure 1) := by
    convert h3.sub (h2.const_mul (3 : ℝ)) using 1
  have h1s : Integrable (fun y : ℝ => 3 * y) (expMeasure 1) := h1.const_mul (3 : ℝ)
  have h123 : Integrable (fun y : ℝ => (y ^ 3 - 3 * y ^ 2) + 3 * y)
      (expMeasure 1) := by
    convert h23.add h1s using 1
  have he : (fun y : ℝ => (y - 1) ^ 3) =
      (fun y : ℝ => (y ^ 3 - 3 * y ^ 2) + 3 * y - 1) := by
    funext y; ring
  rw [he, integral_sub (f := fun y : ℝ => (y ^ 3 - 3 * y ^ 2) + 3 * y)
    (g := fun _ : ℝ => 1) h123
    (integrable_const 1), integral_add (f := fun y : ℝ => y ^ 3 - 3 * y ^ 2)
      (g := fun y : ℝ => 3 * y) h23 h1s,
    integral_sub (f := fun y : ℝ => y ^ 3) (g := fun y : ℝ => 3 * y ^ 2)
      h3 (h2.const_mul 3), integral_const_mul, integral_const_mul,
    (expMeasure_one_nat_moment 3).2, expMeasure_one_integral_sq,
    expMeasure_one_integral_id]
  norm_num

end KLSImprovement.ExponentialMoments
end

#print axioms KLSImprovement.ExponentialMoments.expMeasure_one_exponential_moment
#print axioms KLSImprovement.ExponentialMoments.expMeasure_one_nat_moment
#print axioms KLSImprovement.ExponentialMoments.expMeasure_one_integral_centered
#print axioms KLSImprovement.ExponentialMoments.expMeasure_one_variance_centered
#print axioms KLSImprovement.ExponentialMoments.expMeasure_one_evariance_centered
#print axioms KLSImprovement.ExponentialMoments.expMeasure_one_integral_centered_cube

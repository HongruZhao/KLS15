import KLS4Research.ExponentialSharpness
import ScalarExponentialAppellBridge
import ProductOriginalClassFour

/-! The matching lower bound on the original Euclidean, locally Lipschitz L2
Poincare interface. All witness functions and gradient energies are actual.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace KLS4Research.ExponentialOriginalSharpness
open KLS KLSImprovement.ActualProductCumulants KLSImprovement.ProductAdmissible
open KLSImprovement.ScalarExponentialBridge KLS4Research.ExponentialSharpness

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)
local instance : IsProbabilityMeasure (centeredProductMeasure 1) :=
  centeredProduct_isProbability 1

def centeredScalarMap (y : ℝ) : Space 1 := scalarEmbed (y - 1)

theorem centered_eq_scalar_map : centeredProductMeasure 1 =
    (expMeasure 1).map centeredScalarMap := by
  rw [centeredProduct_eq_raw_map, raw_eq_scalar_map,
    Measure.map_map (centerAffine 1).continuous.measurable scalarEmbed.continuous.measurable]
  congr 1
  funext y
  apply PiLp.ext
  intro i
  change (-1 : ℝ) + y = y - 1
  ring

def trial (a : ℝ) (x : Space 1) : ℝ := Real.exp (a * (x 0 + 1))

theorem trial_comp_map (a : ℝ) : trial a ∘ centeredScalarMap = scalarTrial a := by
  funext y
  simp [trial, centeredScalarMap, scalarEmbed_apply, scalarTrial]

theorem trial_contDiff (a : ℝ) : ContDiff ℝ 1 (trial a) := by
  unfold trial
  fun_prop

theorem trial_memLp (a : ℝ) (ha : a < 1 / 2) :
    MemLp (trial a) 2 (centeredProductMeasure 1) := by
  rw [centered_eq_scalar_map]
  apply (memLp_map_measure_iff (by unfold trial; fun_prop)
    (by unfold centeredScalarMap; fun_prop)).mpr
  rw [trial_comp_map]
  exact scalarTrial_memLp a ha

theorem trial_integral_sq (a : ℝ) (ha : a < 1 / 2) :
    (∫ x, trial a x ^ 2 ∂centeredProductMeasure 1) = 1 / (1 - 2 * a) := by
  rw [centered_eq_scalar_map, integral_map
    (by unfold centeredScalarMap; fun_prop) (by unfold trial; fun_prop)]
  have he : (fun y => trial a (centeredScalarMap y) ^ 2) =
      (fun y => scalarTrial a y ^ 2) := by
    funext y
    rw [show trial a (centeredScalarMap y) = scalarTrial a y from congrFun (trial_comp_map a) y]
  rw [he]
  exact scalarTrial_integral_sq a ha

theorem trial_real_variance (a : ℝ) (ha : a < 1 / 2) :
    ProbabilityTheory.variance (trial a) (centeredProductMeasure 1) =
      1 / (1 - 2 * a) - (1 / (1 - a)) ^ 2 := by
  rw [centered_eq_scalar_map, variance_map
    (by unfold trial; fun_prop) (by unfold centeredScalarMap; fun_prop), trial_comp_map]
  exact scalarTrial_variance a ha

theorem trial_coordinateDerivative (a : ℝ) (x : Space 1) :
    coordinateDerivative (trial a) 0 x = a * trial a x := by
  let P : Space 1 →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)
  have hp : HasFDerivAt (fun z : Space 1 => z 0) P x := P.hasFDerivAt
  have h := ((hp.add_const 1).const_mul a).exp
  have hd : HasFDerivAt (trial a)
      ((a * trial a x) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)) x := by
    unfold trial
    simpa [P, smul_smul, mul_comm] using h
  rw [coordinateDerivative, hd.fderiv]
  simp

theorem trial_gradient_norm_sq (a : ℝ) (x : Space 1) :
    ‖gradient (trial a) x‖ ^ 2 = a ^ 2 * trial a x ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_one, ← coordinateDerivative_eq_gradient,
    trial_coordinateDerivative, mul_pow]

theorem trial_energy (a : ℝ) (ha : a < 1 / 2) :
    energy (centeredProductMeasure 1) (trial a) =
      ENNReal.ofReal (a ^ 2 / (1 - 2 * a)) := by
  unfold energy
  simp_rw [trial_gradient_norm_sq]
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((trial_memLp a ha).integrable_sq.const_mul (a ^ 2))
    (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg a) (sq_nonneg (trial a x))),
    integral_const_mul, trial_integral_sq a ha]
  congr 1
  ring

theorem four_le_every_product_constant {C : ℝ≥0}
    (hC : C ∈ poincareConstants (centeredProductMeasure 1)) : (4 : ℝ) ≤ C := by
  apply four_le_scalar_constant (C : ℝ)
  intro a ha ha2
  have hb := hC (trial a) ⟨(trial_contDiff a).locallyLipschitz, trial_memLp a ha2⟩
  have hfin : (C : ℝ≥0∞) * energy (centeredProductMeasure 1) (trial a) ≠ ⊤ := by
    rw [trial_energy a ha2]
    finiteness
  have hr := ENNReal.toReal_mono hfin hb
  change ProbabilityTheory.variance (trial a) (centeredProductMeasure 1) ≤ _ at hr
  rw [trial_real_variance a ha2, ENNReal.toReal_mul, ENNReal.coe_toReal,
    trial_energy a ha2, ENNReal.toReal_ofReal
      (KLS.RouteArithmetic.exponential_energy_expression_pos a ha ha2).le] at hr
  rwa [scalarTrial_variance a ha2, scalarTrial_energy a ha2]

theorem exponential_poincareConstant_lower_four :
    (4 : ℝ≥0∞) ≤ poincareConstant (centeredProductMeasure 1) := by
  apply le_poincareConstant_of_forall
  intro C hC
  exact_mod_cast four_le_every_product_constant hC

/-- The actual centered rate-one exponential has optimal value exactly four
on the project's unchanged original locally Lipschitz L2 test class. -/
theorem exponential_poincareConstant_eq_four :
    poincareConstant (centeredProductMeasure 1) = 4 := by
  exact le_antisymm
    (KLSImprovement.ProductOriginalFour.product_poincareConstant_le_four 1)
    exponential_poincareConstant_lower_four

/-- This rules out every universal constant below four; it does not prove
the universal upper bound four. -/
theorem universal_poincareConstant_lower_four : (4 : ℝ≥0∞) ≤ universalPoincareConstant :=
  exponential_poincareConstant_lower_four.trans
    (poincareConstant_le_universal (by norm_num) (centeredProduct_admissible 1))

end KLS4Research.ExponentialOriginalSharpness
#print axioms KLS4Research.ExponentialOriginalSharpness.trial_energy
#print axioms KLS4Research.ExponentialOriginalSharpness.exponential_poincareConstant_eq_four
#print axioms KLS4Research.ExponentialOriginalSharpness.universal_poincareConstant_lower_four

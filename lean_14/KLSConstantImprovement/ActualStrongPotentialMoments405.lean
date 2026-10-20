import KLS.FaithfulFullTaylorCriterion
import KLS.WeightedNormExponential
import KLS.WhitenedCutoffMoments

/-! The actual global smooth strongly convex target potential supplies the
fixed integrable dominators for soft-barrier target approximation. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped Topology NNReal ContDiff
namespace KLSConstantImprovement.ActualStrongPotentialMoments405
open KLS
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {V : Space n → ℝ} {κ : ℝ}

theorem strongPotential_norm_pow_integrable (hV : ContDiff ℝ 2 V)
    (hκ : 0 < κ) (hs : StrongConvexOn univ κ V) (m : ℕ) :
    Integrable (fun x => ‖x‖ ^ m) (potentialMeasure V) := by
  simpa only [zero_mul, Real.exp_zero, mul_one] using
    integrable_norm_pow_mul_exp_norm_potentialMeasure hV hκ
      (coordinateHessian_lower_of_strongConvexOn hV hs) m 0

theorem strongPotential_const_integrable (hV : ContDiff ℝ 2 V)
    (hκ : 0 < κ) (hs : StrongConvexOn univ κ V) :
    Integrable (fun _ : Space n => (1 : ℝ)) (potentialMeasure V) := by
  simpa only [pow_zero] using strongPotential_norm_pow_integrable hV hκ hs 0

theorem strongPotential_isFiniteMeasure (hV : ContDiff ℝ 2 V)
    (hκ : 0 < κ) (hs : StrongConvexOn univ κ V) :
    IsFiniteMeasure (potentialMeasure V) :=
  (integrable_const_iff_isFiniteMeasure (by norm_num : (1 : ℝ) ≠ 0)).mp
    (strongPotential_const_integrable hV hκ hs)

theorem strongPotential_polynomial_growth_integrable (hV : ContDiff ℝ 2 V)
    (hκ : 0 < κ) (hs : StrongConvexOn univ κ V) {f : Space n → ℝ}
    (hf : AEStronglyMeasurable f (potentialMeasure V))
    {m : ℕ} {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖ ^ m)) :
    Integrable f (potentialMeasure V) := by
  have hC : 0 ≤ C := by
    have hh := hb 0
    have hp : 0 < 1 + ‖(0 : Space n)‖ ^ m := by positivity
    exact nonneg_of_mul_nonneg_left ((norm_nonneg (f 0)).trans hh) hp
  apply (((strongPotential_const_integrable hV hκ hs).add
    (strongPotential_norm_pow_integrable hV hκ hs m)).const_mul C).mono' hf
  exact Eventually.of_forall fun x => by
    simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ C * (1 + ‖x‖ ^ m))] using hb x

theorem strongPotential_coordinate_product_integrable (hV : ContDiff ℝ 2 V)
    (hκ : 0 < κ) (hs : StrongConvexOn univ κ V)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → Option (Fin n)) :
    Integrable (fun x => ∏ a, coordinateWithConstant (r a) x) (potentialMeasure V) := by
  apply strongPotential_polynomial_growth_integrable hV hκ hs
    (Continuous.aestronglyMeasurable (continuous_finsetProd _ fun a _ =>
      continuous_coordinateWithConstant (r a)))
    (m := Fintype.card ι) (C := 2 ^ (Fintype.card ι - 1))
  intro x
  calc
    ‖∏ a, coordinateWithConstant (r a) x‖ = ∏ a, ‖coordinateWithConstant (r a) x‖ :=
      norm_prod _ _
    _ ≤ ∏ _a : ι, (1 + ‖x‖) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun a _ => norm_coordinateWithConstant_le (r a) x)
    _ = (1 + ‖x‖) ^ Fintype.card ι := by simp
    _ ≤ 2 ^ (Fintype.card ι - 1) * (1 + ‖x‖ ^ Fintype.card ι) := by
      simpa only [one_pow] using add_pow_le (by norm_num : (0 : ℝ) ≤ 1)
        (norm_nonneg x) (Fintype.card ι)

end KLSConstantImprovement.ActualStrongPotentialMoments405
#print axioms KLSConstantImprovement.ActualStrongPotentialMoments405.strongPotential_norm_pow_integrable
#print axioms KLSConstantImprovement.ActualStrongPotentialMoments405.strongPotential_isFiniteMeasure
#print axioms KLSConstantImprovement.ActualStrongPotentialMoments405.strongPotential_polynomial_growth_integrable
#print axioms KLSConstantImprovement.ActualStrongPotentialMoments405.strongPotential_coordinate_product_integrable

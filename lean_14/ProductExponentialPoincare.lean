import ProductVariance
import ActualChargedCore

/-! Tensorization of the proved scalar exponential compact core.  The regularity
and integrability assumptions below concern actual slices and actual derivatives;
no Poincaré inequality is among the hypotheses. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace KLSImprovement.Tensorization
open KLSImprovement.Exponential
set_option maxHeartbeats 2000000
local instance : IsProbabilityMeasure law := isProbabilityMeasure_expMeasure (by norm_num)

/-- Integrability of the conditional variance follows from boundedness. -/
theorem bounded_slice_variance_integrable {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α × β → ℝ) (hf : StronglyMeasurable f) {C : ℝ}
    (hbound : ∀ p, ‖f p‖ ≤ C) :
    Integrable (fun x => variance (fun y => f (x,y)) ν) μ := by
  have hF : MemLp f 2 (μ.prod ν) :=
    MemLp.of_bound hf.aestronglyMeasurable C (.of_forall hbound)
  let G : α → ℝ := fun x => ∫ y, f (x,y) ∂ν
  have hG : MemLp G 2 μ := MemLp.of_bound
    hf.integral_prod_right'.aestronglyMeasurable C
    (.of_forall fun x => by
      simpa [G] using (norm_integral_le_of_norm_le_const (μ := ν)
        (f := fun y => f (x,y)) (.of_forall fun y => hbound (x,y))))
  have hFy (x : α) : MemLp (fun y => f (x,y)) 2 ν :=
    MemLp.of_bound (hf.comp_measurable measurable_prodMk_left).aestronglyMeasurable C
      (.of_forall fun y => hbound (x,y))
  have he (x : α) : variance (fun y => f (x,y)) ν =
      (∫ y, (f (x,y))^2 ∂ν)-(G x)^2 := variance_eq_sub (hFy x)
  simp_rw [he]
  exact hF.integrable_sq.integral_prod_left.sub hG.integrable_sq

/-- Constant four for two actual exponential coordinates.  Every slice is C¹
and compactly supported; the displayed square-derivative assumptions provide
Fubini integrability. -/
theorem exponential_product_two_poincare (f : ℝ × ℝ → ℝ)
    (hf : StronglyMeasurable f) {C : ℝ} (hbound : ∀ p, ‖f p‖ ≤ C)
    (hfirst : ∀ y, ContDiff ℝ 1 (fun x => f (x,y)))
    (hcfirst : ∀ y, HasCompactSupport (fun x => f (x,y)))
    (hsecond : ∀ x, ContDiff ℝ 1 (fun y => f (x,y)))
    (hcsecond : ∀ x, HasCompactSupport (fun y => f (x,y)))
    (hd1 : Integrable (fun p => (deriv (fun x => f (x,p.2)) p.1)^2) (law.prod law))
    (hd2 : Integrable (fun p => (deriv (fun y => f (p.1,y)) p.2)^2) (law.prod law)) :
    variance f (law.prod law) ≤
      4 * (∫ p, (deriv (fun x => f (x,p.2)) p.1)^2 +
        (deriv (fun y => f (p.1,y)) p.2)^2 ∂law.prod law) := by
  have hvar1 : Integrable (fun y => variance (fun x => f (x,y)) law) law := by
    exact bounded_slice_variance_integrable (fun p : ℝ × ℝ => f (p.2,p.1))
      (hf.comp_measurable measurable_swap) (fun p => hbound (p.2,p.1))
  have hvar2 : Integrable (fun x => variance (fun y => f (x,y)) law) law :=
    bounded_slice_variance_integrable f hf hbound
  have he1 : (∫ y, variance (fun x => f (x,y)) law ∂law) ≤
      4 * (∫ p, (deriv (fun x => f (x,p.2)) p.1)^2 ∂law.prod law) := by
    rw [integral_prod_symm _ hd1, ← integral_const_mul]
    exact integral_mono hvar1 (hd1.integral_prod_right.const_mul 4)
      (fun y => poincare_core (fun x => f (x,y)) (hfirst y) (hcfirst y))
  have he2 : (∫ x, variance (fun y => f (x,y)) law ∂law) ≤
      4 * (∫ p, (deriv (fun y => f (p.1,y)) p.2)^2 ∂law.prod law) := by
    rw [integral_prod _ hd2, ← integral_const_mul]
    exact integral_mono hvar2 (hd2.integral_prod_left.const_mul 4)
      (fun x => poincare_core (fun y => f (x,y)) (hsecond x) (hcsecond x))
  have he := product_variance_efron_stein_two (μ := law) (ν := law) f hf hbound
  rw [integral_add hd1 hd2]
  linarith

end KLSImprovement.Tensorization
#print axioms KLSImprovement.Tensorization.bounded_slice_variance_integrable
#print axioms KLSImprovement.Tensorization.exponential_product_two_poincare

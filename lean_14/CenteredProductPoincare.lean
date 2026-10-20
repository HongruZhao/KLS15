import FiniteProductTensorization

/-! The actual centered product exponential benchmark in every finite dimension.
Coordinates are translated by one; the energy uses ordinary partial derivatives. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace KLSImprovement.Tensorization
open KLSImprovement.Exponential
set_option maxHeartbeats 2000000
local instance : IsProbabilityMeasure law := isProbabilityMeasure_expMeasure (by norm_num)

def centerCoordinates {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => x i - 1
abbrev centeredProductLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  (productLaw n).map centerCoordinates

lemma centerCoordinates_measurable {n : ℕ} :
    Measurable (centerCoordinates : (Fin n → ℝ) → (Fin n → ℝ)) := by
  unfold centerCoordinates
  fun_prop

lemma centerCoordinates_update {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    centerCoordinates (Function.update x i t) =
      Function.update (centerCoordinates x) i (t - 1) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [centerCoordinates]
  · simp [centerCoordinates, Function.update_of_ne h]

lemma coordinateDeriv_center {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i : Fin n)
    (x : Fin n → ℝ) :
    coordinateDeriv (fun y => f (centerCoordinates y)) i x =
      coordinateDeriv f i (centerCoordinates x) := by
  unfold coordinateDeriv
  simp_rw [centerCoordinates_update]
  exact deriv_comp_sub_const (fun t => f (Function.update (centerCoordinates x) i t)) 1 (x i)

/-- The centered product exponential satisfies Poincaré with constant four in
arbitrary dimension on its C¹ compact coordinate core. The explicit bounds and
measurability conditions ensure all the displayed energies are genuine finite
integrals. This theorem assumes no Poincaré inequality or exponential moments. -/
theorem centered_exponential_finite_product_poincare (n : ℕ)
    (f : (Fin n → ℝ) → ℝ) (hf : StronglyMeasurable f) {C D : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ C)
    (hreg : ∀ i x, ContDiff ℝ 1 (fun t => f (Function.update x i t)))
    (hc : ∀ i x, HasCompactSupport (fun t => f (Function.update x i t)))
    (hd : ∀ i, StronglyMeasurable (coordinateDeriv f i))
    (hdb : ∀ i x, ‖coordinateDeriv f i x‖ ≤ D) :
    variance f (centeredProductLaw n) ≤
      4 * (∫ x, ∑ i, (coordinateDeriv f i x)^2 ∂centeredProductLaw n) := by
  let F : (Fin n → ℝ) → ℝ := fun x => f (centerCoordinates x)
  have hF : StronglyMeasurable F := hf.comp_measurable centerCoordinates_measurable
  have hr (i : Fin n) (x : Fin n → ℝ) :
      ContDiff ℝ 1 (fun t => F (Function.update x i t)) := by
    dsimp [F]
    simp_rw [centerCoordinates_update]
    exact (hreg i (centerCoordinates x)).comp (by fun_prop)
  have hcs (i : Fin n) (x : Fin n → ℝ) :
      HasCompactSupport (fun t => F (Function.update x i t)) := by
    dsimp [F]
    simp_rw [centerCoordinates_update]
    simpa [Function.comp_def, Homeomorph.addRight, sub_eq_add_neg] using
      (hc i (centerCoordinates x)).comp_homeomorph (Homeomorph.addRight (-1 : ℝ))
  have hdF (i : Fin n) : StronglyMeasurable (coordinateDeriv F i) := by
    have he : coordinateDeriv F i = fun x => coordinateDeriv f i (centerCoordinates x) := by
      funext x
      exact coordinateDeriv_center f i x
    rw [he]
    exact (hd i).comp_measurable centerCoordinates_measurable
  have hdbF (i : Fin n) (x : Fin n → ℝ) : ‖coordinateDeriv F i x‖ ≤ D := by
    rw [show coordinateDeriv F i x = coordinateDeriv f i (centerCoordinates x) from
      coordinateDeriv_center f i x]
    exact hdb i _
  have he := exponential_finite_product_poincare n F hF
    (fun x => hb (centerCoordinates x)) hr hcs hdF hdbF
  have hvar : variance f (centeredProductLaw n) = variance F (productLaw n) := by
    exact variance_map hf.measurable.aemeasurable centerCoordinates_measurable.aemeasurable
  have henergy : (∫ x, ∑ i, (coordinateDeriv f i x)^2 ∂centeredProductLaw n) =
      ∫ x, ∑ i, (coordinateDeriv F i x)^2 ∂productLaw n := by
    rw [integral_map centerCoordinates_measurable.aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun x => ∑ i, (coordinateDeriv f i x)^2)
        (centeredProductLaw n))]
    apply integral_congr_ae
    exact .of_forall fun x => by
      apply Finset.sum_congr rfl
      intro i _
      rw [show coordinateDeriv F i x = coordinateDeriv f i (centerCoordinates x) from
        coordinateDeriv_center f i x]
  rw [hvar, henergy]
  exact he

end KLSImprovement.Tensorization
#print axioms KLSImprovement.Tensorization.centered_exponential_finite_product_poincare

namespace KLSImprovement.Tensorization
open KLSImprovement.Exponential

lemma coordinateDeriv_eq_fderiv {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : ContDiff ℝ 1 f) (i : Fin n) (x : Fin n → ℝ) :
    coordinateDeriv f i x = fderiv ℝ f x (Pi.single i 1) := by
  have he := ((hf.differentiable one_ne_zero x).hasFDerivAt).comp_hasDerivAt_of_eq (x i)
    (hasDerivAt_update x i (x i)) (by simp : x = Function.update x i (x i))
  exact he.deriv

/-- The usual compact C¹ core formulation, with every measurability,
boundedness, and slice regularity condition discharged from these two standard
hypotheses. The sum of squares is the ordinary Euclidean gradient energy. -/
theorem centered_exponential_product_compact_core (n : ℕ)
    (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    variance f (centeredProductLaw n) ≤
      4 * (∫ x, ∑ i, (coordinateDeriv f i x)^2 ∂centeredProductLaw n) := by
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hf.continuous
  obtain ⟨D,hD⟩ := (hc.fderiv ℝ).exists_bound_of_continuous
    (hf.continuous_fderiv one_ne_zero)
  have hd (i : Fin n) : Continuous (coordinateDeriv f i) := by
    have he : coordinateDeriv f i = fun x => fderiv ℝ f x (Pi.single i 1) :=
      funext (coordinateDeriv_eq_fderiv f hf i)
    rw [he]
    exact (hf.continuous_fderiv_apply one_ne_zero).comp
      (continuous_id.prodMk continuous_const)
  apply centered_exponential_finite_product_poincare n f hf.continuous.stronglyMeasurable hC
    (fun i x => hf.comp (contDiff_update 1 x i))
    (fun i x => hc.comp_isClosedEmbedding (isClosedEmbedding_update x i))
    (fun i => (hd i).stronglyMeasurable)
  intro i x
  rw [coordinateDeriv_eq_fderiv f hf i x]
  calc
    ‖fderiv ℝ f x (Pi.single i 1)‖ ≤ ‖fderiv ℝ f x‖ * ‖(Pi.single i (1 : ℝ) : Fin n → ℝ)‖ :=
      (fderiv ℝ f x).le_opNorm _
    _ = ‖fderiv ℝ f x‖ := by simp only [Pi.norm_single, norm_one, mul_one]
    _ ≤ D := hD x

end KLSImprovement.Tensorization
#print axioms KLSImprovement.Tensorization.centered_exponential_product_compact_core

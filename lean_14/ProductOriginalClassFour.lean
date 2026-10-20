import CenteredProductPoincare
import ActualProductAdmissible
import KLS.FaithfulPoincareSmoothCore
import KLS.LogConcavityAbsoluteContinuity

/-! Extend the actual finite-product exponential upper bound from its compact
C1 core to the original KLS locally Lipschitz L2 test class. The ordinary
Euclidean coordinate energy is transported explicitly. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace KLSImprovement.ProductOriginalFour
open KLS KLSImprovement.ActualProductCumulants KLSImprovement.ProductAdmissible
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def euclideanCoordinates (n : ℕ) : (Fin n → ℝ) ≃L[ℝ] Space n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm

theorem centered_measure_as_map (n : ℕ) :
    centeredProductMeasure n =
      (KLSImprovement.Tensorization.centeredProductLaw n).map (euclideanCoordinates n) := by
  rw [KLSImprovement.Tensorization.centeredProductLaw,
    Measure.map_map (euclideanCoordinates n).continuous.measurable
      KLSImprovement.Tensorization.centerCoordinates_measurable]
  rfl

theorem transported_coordinate_derivative {n : ℕ} (f : Space n → ℝ)
    (hf : ContDiff ℝ 1 f) (i : Fin n) (x : Fin n → ℝ) :
    KLSImprovement.Tensorization.coordinateDeriv (f ∘ euclideanCoordinates n) i x =
      coordinateDerivative f i (euclideanCoordinates n x) := by
  rw [KLSImprovement.Tensorization.coordinateDeriv_eq_fderiv _
    (hf.comp (euclideanCoordinates n).contDiff)]
  unfold coordinateDerivative
  rw [fderiv_comp x (hf.differentiable one_ne_zero _)
    (euclideanCoordinates n).differentiableAt]
  simp only [ContinuousLinearEquiv.fderiv, ContinuousLinearMap.comp_apply]
  rfl

theorem product_compact_euclidean_core (n : ℕ) (f : Space n → ℝ)
    (hf : ContDiff ℝ 3 f) (hc : HasCompactSupport f) :
    ProbabilityTheory.variance f (centeredProductMeasure n) ≤
      4 * ∑ i : Fin n, ∫ x, (coordinateDerivative f i x)^2 ∂centeredProductMeasure n := by
  let μ := centeredProductMeasure n
  let e := euclideanCoordinates n
  let : IsProbabilityMeasure μ := centeredProduct_isProbability n
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hg : ContDiff ℝ 1 (f ∘ e) := hf1.comp e.contDiff
  have hgcs : HasCompactSupport (f ∘ e) := hc.comp_homeomorph e.toHomeomorph
  have hb := KLSImprovement.Tensorization.centered_exponential_product_compact_core n
    (f ∘ e) hg hgcs
  have hvar : ProbabilityTheory.variance f μ =
      ProbabilityTheory.variance (f ∘ e) (KLSImprovement.Tensorization.centeredProductLaw n) := by
    rw [show μ = (KLSImprovement.Tensorization.centeredProductLaw n).map e from centered_measure_as_map n]
    exact variance_map hf.continuous.measurable.aemeasurable e.continuous.measurable.aemeasurable
  have hd (i : Fin n) : Continuous (coordinateDerivative f i) := by
    exact (hf1.continuous_fderiv_apply one_ne_zero).comp
      (continuous_id.prodMk continuous_const)
  obtain ⟨D, hD⟩ := (hc.fderiv ℝ).exists_bound_of_continuous
    (hf1.continuous_fderiv one_ne_zero)
  have hdi (i : Fin n) : Integrable (fun x => (coordinateDerivative f i x)^2) μ := by
    apply MemLp.integrable_sq
    apply (memLp_const (μ := μ) (p := 2) D).mono' (hd i).aestronglyMeasurable
    exact .of_forall (fun x => by
      calc
        ‖coordinateDerivative f i x‖ ≤ ‖fderiv ℝ f x‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ :=
          (fderiv ℝ f x).le_opNorm _
        _ = ‖fderiv ℝ f x‖ := by simp
        _ ≤ D := hD x)
  have he : (∫ x, ∑ i, (KLSImprovement.Tensorization.coordinateDeriv (f ∘ e) i x)^2
      ∂KLSImprovement.Tensorization.centeredProductLaw n) =
        ∑ i, ∫ x, (coordinateDerivative f i x)^2 ∂μ := by
    rw [←integral_finsetSum Finset.univ (fun i _ => hdi i)]
    rw [show μ = (KLSImprovement.Tensorization.centeredProductLaw n).map e from centered_measure_as_map n]
    rw [integral_map e.continuous.measurable.aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun x => ∑ i, (coordinateDerivative f i x)^2)
        ((KLSImprovement.Tensorization.centeredProductLaw n).map e))]
    apply integral_congr_ae
    exact .of_forall (fun x => by
      apply Finset.sum_congr rfl
      intro i _
      rw [transported_coordinate_derivative f hf1 i x])
  rw [hvar, ←he]
  exact hb

/-- No compact-support or differentiability hypothesis is added to the
original locally Lipschitz L2 class. -/
theorem product_four_mem (n : ℕ) :
    (4 : ℝ≥0) ∈ poincareConstants (centeredProductMeasure n) := by
  let : IsProbabilityMeasure (centeredProductMeasure n) := centeredProduct_isProbability n
  apply mem_poincareConstants_of_compact_smooth_tests
    (centeredProduct_admissible n).absolutelyContinuousLebesgue (by norm_num)
  intro f hf hc
  exact product_compact_euclidean_core n f hf hc

theorem product_poincare_four {n : ℕ} {f : Space n → ℝ}
    (hf : LocallyLipschitzTests (centeredProductMeasure n) f) :
    KLS.variance (centeredProductMeasure n) f ≤
      (4 : ℝ≥0∞) * energy (centeredProductMeasure n) f := by
  simpa using product_four_mem n f hf

theorem product_poincareConstant_le_four (n : ℕ) :
    poincareConstant (centeredProductMeasure n) ≤ 4 := by
  simpa using poincareConstant_le_of_mem (product_four_mem n)

end KLSImprovement.ProductOriginalFour
#print axioms KLSImprovement.ProductOriginalFour.centered_measure_as_map
#print axioms KLSImprovement.ProductOriginalFour.transported_coordinate_derivative
#print axioms KLSImprovement.ProductOriginalFour.product_compact_euclidean_core
#print axioms KLSImprovement.ProductOriginalFour.product_four_mem
#print axioms KLSImprovement.ProductOriginalFour.product_poincare_four
#print axioms KLSImprovement.ProductOriginalFour.product_poincareConstant_le_four

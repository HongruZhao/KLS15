import KLSConstantImprovement.ActualSourceGlobalRawHessianEvolution405
import KLSConstantImprovement.ActualSourceTensorGramMetricBinding
import KLSConstantImprovement.ActualSourceHessianFormEquation405

/-! Actual global Hessian testing with the Hessian and quadratic tensor
Gram fields. These use the constructed C1,1 Hessian and its genuine weak
third derivative. All global metric energies and bounded L1 curvature
products are paid by the actual source; no C4 regularity or global lower
Hessian bound is assumed. -/
noncomputable section
open MeasureTheory Matrix Set Filter InnerProductSpace
open scoped BigOperators ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceHessianPolynomialTests405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualCompactRawMetricGraph ActualSourceHessianEvolution405
open ActualSourceTensorGramMetricBinding ActualSourceGlobalRawHessianEvolution405
open ActualSourceHessianFormEquation405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_hessian_polynomial_bounded (d : SourceData μ)
    (g : Matrix (Fin n) (Fin n) ℝ → ℝ) (hg : Continuous g) :
    AEStronglyMeasurable (fun x => g (coordinateHessian d.potential x))
      (potentialMeasure d.potential) ∧
    ∃ B : ℝ, ∀ x, ‖g (coordinateHessian d.potential x)‖ ≤ B := by
  refine ⟨(hg.measurable.comp (measurable_coordinateHessian d.potential)).aestronglyMeasurable, ?_⟩
  obtain ⟨B, hB⟩ := d.hessian_range_bounded.isCompact_closure.bddAbove_image hg.norm.continuousOn
  exact ⟨B, fun x => hB ⟨coordinateHessian d.potential x, subset_closure ⟨x, rfl⟩, rfl⟩⟩

theorem actual_global_hessian_entry_test (d : SourceData μ) (i j k l : Fin n) :
    (∫ x, ∑ r,
      rawCanonicalMetricDerivative d.potential (fun a y => d.third y a i j) r x *
        rawCanonicalMetricDerivative d.potential (fun a y => d.third y a k l) r x
          ∂potentialMeasure d.potential) =
      ∫ x, (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) *
        coordinateHessian d.potential x k l ∂potentialMeasure d.potential := by
  exact actual_global_bounded_raw_hessian_evolution d
    (d.hessian_entry_memLp k l 2).aestronglyMeasurable
    (fun x => coordinateHessian_entry_bound_of_gradient_lipschitz d.gradient_lipschitz x k l)
    (fun a E hE => d.third_local_L2 a k l E hE)
    (fun a => d.third_weak_derivative a k l) (d.hessian_entry_raw_metric_memLp k l) i j

theorem actual_global_hessian_tensorGram_test (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j k l : Fin n) :
    (∫ x, ∑ r,
      rawCanonicalMetricDerivative d.potential (fun a y => d.third y a i j) r x *
        rawCanonicalMetricDerivative d.potential
          (sourceTensorGramRawDerivative d.potential d.third T k l) r x
            ∂potentialMeasure d.potential) =
      ∫ x, (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) *
        (T k * coordinateHessian d.potential x * T l * coordinateHessian d.potential x).trace
          ∂potentialMeasure d.potential := by
  let g : Matrix (Fin n) (Fin n) ℝ → ℝ := fun H => (T k * H * T l * H).trace
  have hg : Continuous g := by fun_prop
  obtain ⟨hm, B, hb⟩ := actual_hessian_polynomial_bounded d g hg
  have heq : sourceTensorGramEntry d.potential T k l =
      fun x => g (coordinateHessian d.potential x) :=
    funext (sourceTensorGramEntry_eq_trace d.potential T k l)
  have he := actual_global_bounded_raw_hessian_evolution d
    (heq.symm ▸ hm) (fun x => by rw [heq]; exact hb x)
    (fun a E hE => d.tensorGram_derivative_local_L2 T k l a E hE)
    (fun a => d.tensorGram_hasLocalWeakCoordinateDerivative T k l a)
    (d.tensorGram_raw_metric_memLp T k l) i j
  simpa only [sourceTensorGramEntry_eq_trace] using he

theorem actual_hessian_form_cross_identity (d : SourceData μ) (i j k l : Fin n) :
    canonicalMetricEnergy d.potential (actualHessianForm d i j) (actualHessianForm d k l) =
      ∫ x, (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) *
        coordinateHessian d.potential x k l ∂potentialMeasure d.potential := by
  rw [canonicalMetricEnergy_apply]
  have he (r : Fin n) :
      inner ℝ (canonicalMetricGradient d.potential r (actualHessianForm d i j))
        (canonicalMetricGradient d.potential r (actualHessianForm d k l)) =
      ∫ x, rawCanonicalMetricDerivative d.potential (fun a y => d.third y a i j) r x *
        rawCanonicalMetricDerivative d.potential (fun a y => d.third y a k l) r x
          ∂potentialMeasure d.potential := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [actualHessianForm_gradient_ae d i j r,
      actualHessianForm_gradient_ae d k l r] with x hx hy
    simp only [RCLike.inner_apply, conj_trivial, hx, hy]
    ring
  simp_rw [he]
  have hi (r : Fin n) : Integrable (fun x =>
      rawCanonicalMetricDerivative d.potential (fun a y => d.third y a i j) r x *
        rawCanonicalMetricDerivative d.potential (fun a y => d.third y a k l) r x)
          (potentialMeasure d.potential) :=
    (d.hessian_entry_raw_metric_memLp i j r).integrable_mul
      (d.hessian_entry_raw_metric_memLp k l r)
  rw [← integral_finsetSum Finset.univ (fun r _ => hi r)]
  exact actual_global_hessian_entry_test d i j k l

end KLSConstantImprovement.ActualSourceHessianPolynomialTests405
#print axioms KLSConstantImprovement.ActualSourceHessianPolynomialTests405.actual_global_hessian_entry_test
#print axioms KLSConstantImprovement.ActualSourceHessianPolynomialTests405.actual_global_hessian_tensorGram_test
#print axioms KLSConstantImprovement.ActualSourceHessianPolynomialTests405.actual_hessian_form_cross_identity

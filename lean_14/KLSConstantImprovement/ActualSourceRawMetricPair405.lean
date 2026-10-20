import KLSConstantImprovement.ActualSourceHessianMetricBinding
import KLSConstantImprovement.ActualSourceGlobalCurvature405

/-! Actual inverse-Hessian pairings are literal L2 metric-gradient
pairings. The actual Hessian flux uses the same genuine weak third
tensor, so all mixed finite-energy test pairings are integrable. -/
noncomputable section
open MeasureTheory Matrix Set Filter
open scoped BigOperators ContDiff ENNReal
namespace KLSConstantImprovement.ActualSourceRawMetricPair405
open KLS ActualBoundedCanonicalSource ActualCompactRawMetricGraph
open ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricCore
open ActualSourceHessianEvolution405 ActualSourceGlobalCurvature405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_raw_metric_pair_ae (d : SourceData μ)
    (F G : Fin n → Space n → ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      (∑ r, rawCanonicalMetricDerivative d.potential F r x *
        rawCanonicalMetricDerivative d.potential G r x) =
      ∑ a, ∑ b, (coordinateHessian d.potential x)⁻¹ a b * F a x * G b x := by
  filter_upwards [d.hessian_ae_source] with x hx
  let R := canonicalMetricRoot d.potential x
  let f : Fin n → ℝ := fun i => F i x
  let g : Fin n → ℝ := fun i => G i x
  change (R *ᵥ f) ⬝ᵥ (R *ᵥ g) = _
  rw [dotProduct_comm (R *ᵥ f) (R *ᵥ g),
    ← Matrix.dotProduct_transpose_mulVec R f (R *ᵥ g),
    Matrix.mulVec_mulVec, canonicalMetricRoot_gram_at hx.1]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, f, g]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem actual_raw_metric_pair_integrable (d : SourceData μ)
    (F G : Fin n → Space n → ℝ)
    (hF : ∀ r, MemLp (rawCanonicalMetricDerivative d.potential F r) 2
      (potentialMeasure d.potential))
    (hG : ∀ r, MemLp (rawCanonicalMetricDerivative d.potential G r) 2
      (potentialMeasure d.potential)) :
    Integrable (fun x => ∑ a, ∑ b,
      (coordinateHessian d.potential x)⁻¹ a b * F a x * G b x)
      (potentialMeasure d.potential) := by
  have hI : Integrable (fun x => ∑ r, rawCanonicalMetricDerivative d.potential F r x *
      rawCanonicalMetricDerivative d.potential G r x) (potentialMeasure d.potential) :=
    integrable_finsetSum Finset.univ (fun r _ => (hF r).integrable_mul (hG r))
  exact hI.congr (actual_raw_metric_pair_ae d F G)

theorem actual_hessian_flux_metric_pair_ae (d : SourceData μ)
    (F : Fin n → Space n → ℝ) (i j : Fin n) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      (∑ a, ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j * F a x) =
      ∑ r, rawCanonicalMetricDerivative d.potential (fun a y => d.third y a i j) r x *
        rawCanonicalMetricDerivative d.potential F r x := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) :=
    withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source, d.third_symmetric_ae.filter_mono hac.ae_le,
    actual_raw_metric_pair_ae d (fun a y => d.third y a i j) F] with x hx hN hP
  rw [hP]
  exact actual_hessian_flux_contraction _ hx.1.inv.posSemidef.isHermitian.isSymm
    (sourceThirdMatrix d x) (fun k a b => (hN k a b).1) (fun a => F a x) i j

end KLSConstantImprovement.ActualSourceRawMetricPair405
#print axioms KLSConstantImprovement.ActualSourceRawMetricPair405.actual_raw_metric_pair_ae
#print axioms KLSConstantImprovement.ActualSourceRawMetricPair405.actual_raw_metric_pair_integrable
#print axioms KLSConstantImprovement.ActualSourceRawMetricPair405.actual_hessian_flux_metric_pair_ae

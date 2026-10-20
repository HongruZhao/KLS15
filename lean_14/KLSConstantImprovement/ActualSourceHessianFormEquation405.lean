import KLSConstantImprovement.ActualSourceHessianMetricBinding
import KLSConstantImprovement.ActualSourceGlobalCurvature405
import KLS.WeightedResolventWeakEquation

/-!
The actual source Hessian belongs to the canonical form graph through its
genuine weak third tensor. Its compact weak matrix evolution is identified
with that same form energy, using the actual inverse-root Gram identity.
No classical derivative of H and no L2 domain for AH are asserted.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Matrix Set Filter InnerProductSpace
open scoped BigOperators ContDiff Topology RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceHessianFormEquation405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualWeakCanonicalMetricCore ActualCompactRawMetricGraph
open ActualSourceHessianEvolution405 ActualSourceGlobalCurvature405
variable {n : ℕ} {μ : Measure (Space n)}

def actualHessianForm (d : SourceData μ) (k l : Fin n) : CanonicalMetricH1 d.potential :=
  Classical.choose (d.exists_hessian_entry_metricH1 k l)

theorem actualHessianForm_value_ae (d : SourceData μ) (k l : Fin n) :
    (canonicalMetricValue d.potential (actualHessianForm d k l) : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential] fun x => coordinateHessian d.potential x k l -
        ∫ y, coordinateHessian d.potential y k l ∂potentialMeasure d.potential :=
  (Classical.choose_spec (d.exists_hessian_entry_metricH1 k l)).1

theorem actualHessianForm_gradient_ae (d : SourceData μ) (k l i : Fin n) :
    (canonicalMetricGradient d.potential i (actualHessianForm d k l) : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential]
        rawCanonicalMetricDerivative d.potential (fun a x => d.third x a k l) i :=
  (Classical.choose_spec (d.exists_hessian_entry_metricH1 k l)).2 i

theorem actualHessianForm_value (d : SourceData μ) (k l : Fin n) :
    letI := d.source_probability
    canonicalMetricValue d.potential (actualHessianForm d k l) =
      CenteredL2.center (potentialMeasure d.potential)
        ((d.hessian_entry_memLp k l 2).toLp (fun x => coordinateHessian d.potential x k l)) := by
  letI := d.source_probability
  let h := (d.hessian_entry_memLp k l 2).toLp (fun x => coordinateHessian d.potential x k l)
  have hh : (h : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      fun x => coordinateHessian d.potential x k l := (d.hessian_entry_memLp k l 2).coeFn_toLp
  have hmean : (∫ x, h x ∂potentialMeasure d.potential) =
      ∫ x, coordinateHessian d.potential x k l ∂potentialMeasure d.potential :=
    integral_congr_ae hh
  apply Lp.ext
  filter_upwards [actualHessianForm_value_ae d k l,
    CenteredL2.center_ae (potentialMeasure d.potential) h, hh] with x hx hc hhx
  rw [hc, hhx, hmean]
  exact hx

theorem raw_metric_hessian_flux_pair_ae (d : SourceData μ) (k l : Fin n)
    (p : Space n → Fin n → ℝ) :
    (fun x => ∑ i : Fin n,
      rawCanonicalMetricDerivative d.potential (fun a y => d.third y a k l) i x *
        (canonicalMetricRoot d.potential x *ᵥ p x) i)
      =ᵐ[potentialMeasure d.potential] fun x => ∑ a : Fin n,
        ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x k) a l * p x a := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) :=
    withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source, d.third_symmetric_ae.filter_mono hac.ae_le] with x hx hN
  let R := canonicalMetricRoot d.potential x
  let F : Fin n → ℝ := fun a => d.third x a k l
  have hpair : (R *ᵥ F) ⬝ᵥ (R *ᵥ p x) =
      F ⬝ᵥ ((coordinateHessian d.potential x)⁻¹ *ᵥ p x) := by
    calc
      _ = (R *ᵥ p x) ⬝ᵥ (R *ᵥ F) := dotProduct_comm _ _
      _ = F ⬝ᵥ (R.transpose *ᵥ (R *ᵥ p x)) :=
        (Matrix.dotProduct_transpose_mulVec R F (R *ᵥ p x)).symm
      _ = _ := by rw [Matrix.mulVec_mulVec, canonicalMetricRoot_gram_at hx.1]
  change (R *ᵥ F) ⬝ᵥ (R *ᵥ p x) = _
  rw [hpair, actual_hessian_flux_contraction _ hx.1.posSemidef.inv.isHermitian.isSymm
    (sourceThirdMatrix d x) (fun a b c => (hN a b c).1) (p x) k l]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change d.third x a k l * ((coordinateHessian d.potential x)⁻¹ a b * p x b) =
    (coordinateHessian d.potential x)⁻¹ a b * d.third x a k l * p x b
  ring

/-- The weak matrix PDE and the completed form are the same actual
operator on compact tests; every metric-gradient product is integrable. -/
theorem actual_hessian_form_compact_evolution (d : SourceData μ) (k l : Fin n)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (V : CanonicalMetricH1 d.potential)
    (hVd : ∀ i : Fin n, (canonicalMetricGradient d.potential i V : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential] canonicalMetricDerivative d.potential ψ i) :
    canonicalMetricEnergy d.potential (actualHessianForm d k l) V =
      ∫ x, (coordinateHessian d.potential x k l - sourceConnectionCurvature d x k l) *
        ψ x ∂potentialMeasure d.potential := by
  have hd (i : Fin n) : MemLp (canonicalMetricDerivative d.potential ψ i) 2
      (potentialMeasure d.potential) :=
    (memLp_congr_ae (hVd i)).mp (Lp.memLp (canonicalMetricGradient d.potential i V))
  have hi (i : Fin n) : Integrable (fun x =>
      rawCanonicalMetricDerivative d.potential (fun a y => d.third y a k l) i x *
        canonicalMetricDerivative d.potential ψ i x) (potentialMeasure d.potential) :=
    (d.hessian_entry_raw_metric_memLp k l i).integrable_mul (hd i)
  have hinner (i : Fin n) :
      inner ℝ (canonicalMetricGradient d.potential i (actualHessianForm d k l))
        (canonicalMetricGradient d.potential i V) =
      ∫ x, rawCanonicalMetricDerivative d.potential (fun a y => d.third y a k l) i x *
        canonicalMetricDerivative d.potential ψ i x ∂potentialMeasure d.potential := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [actualHessianForm_gradient_ae d k l i, hVd i] with x hu hv
    simp only [RCLike.inner_apply, conj_trivial, hu, hv]
    ring
  have he := actual_compact_hessian_evolution d hψ hc k l
  have hform : canonicalMetricEnergy d.potential (actualHessianForm d k l) V =
      ∑ a, ∫ x, ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x k) a l *
        coordinateDerivative ψ a x ∂potentialMeasure d.potential := by
    rw [canonicalMetricEnergy_apply]
    simp_rw [hinner]
    rw [← integral_finsetSum Finset.univ (fun i _ => hi i),
      ← integral_finsetSum Finset.univ (fun a _ => he.1 a)]
    exact integral_congr_ae (raw_metric_hessian_flux_pair_ae d k l
      (fun x a => coordinateDerivative ψ a x))
  have hneg : (∫ x, (coordinateHessian d.potential x k l - sourceConnectionCurvature d x k l) *
      ψ x ∂potentialMeasure d.potential) =
      -(∫ x, (-coordinateHessian d.potential x k l + sourceConnectionCurvature d x k l) *
        ψ x ∂potentialMeasure d.potential) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  rw [hform, hneg]
  linarith [he.2.2]

end KLSConstantImprovement.ActualSourceHessianFormEquation405

#print axioms KLSConstantImprovement.ActualSourceHessianFormEquation405.actualHessianForm_value
#print axioms KLSConstantImprovement.ActualSourceHessianFormEquation405.raw_metric_hessian_flux_pair_ae
#print axioms KLSConstantImprovement.ActualSourceHessianFormEquation405.actual_hessian_form_compact_evolution

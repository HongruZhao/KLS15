import KLSConstantImprovement.ActualBoundedSourceCalculus
import KLSConstantImprovement.ActualSourceGradientCoefficientPassage405
import KLSConstantImprovement.ActualSourceLimitMetricRelations405

/-! The actual raw canonical gradient of every C1 target pullback is
globally bounded on the bounded target source.  This pays the forcing
gradient domain for quadratic eta rows; it does not assert bounded eta mass. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourcePullbackMetricGradient405
open KLS ActualBoundedCanonicalSource ActualSourceGradientCoefficientPassage405
open ActualSourceLimitFluxDomains405 ActualCompactRawMetricGraph
open ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricOrdinaryGraph
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem canonicalMetricRoot_mul_hessian_at {φ : Space n → ℝ} {x : Space n}
    (hp : (coordinateHessian φ x).PosDef) :
    canonicalMetricRoot φ x * coordinateHessian φ x = canonicalMetricUnroot φ x := by
  have he := congrArg Matrix.transpose (hessian_mul_canonicalMetricRoot_at hp)
  have hr : (canonicalMetricRoot φ x).IsSymm := inverseSqrtMatrix_isSymm (coordinateHessian φ x)
  have hs : (canonicalMetricUnroot φ x).IsSymm :=
    (inverseSqrtMatrix_isSymm (coordinateHessian φ x)).inv
  simpa only [Matrix.transpose_mul, hr.eq,
    hp.isHermitian.isSymm.eq, hs.eq] using he

def pullbackRawGradient (d : SourceData μ) (f : Space n → ℝ) (i : Fin n) (x : Space n) : ℝ :=
  inner ℝ (gradient f (gradient d.potential x))
    (matrixAction (coordinateHessian d.potential x) (EuclideanSpace.single i 1))

theorem pullback_raw_metric_gradient_ae (d : SourceData μ) (f : Space n → ℝ) (i : Fin n) :
    rawCanonicalMetricDerivative d.potential (pullbackRawGradient d f) i
      =ᵐ[potentialMeasure d.potential] fun x =>
        ∑ a : Fin n, canonicalMetricUnroot d.potential x i a * gradient f (gradient d.potential x) a := by
  filter_upwards [d.hessian_ae_source] with x hp
  let v := gradient f (gradient d.potential x)
  have hF : (fun a => pullbackRawGradient d f a x) =
      coordinateHessian d.potential x *ᵥ (fun a => v a) := by
    funext a
    have he := inner_matrixAction_transpose (coordinateHessian d.potential x) v (EuclideanSpace.single a 1)
    rw [hp.1.isHermitian.isSymm.eq] at he
    change inner ℝ v (matrixAction (coordinateHessian d.potential x) (EuclideanSpace.single a 1)) = _
    rw [← he]
    rw [EuclideanSpace.inner_single_right]
    simp [matrixAction_apply, Matrix.mulVec, dotProduct]
  change (canonicalMetricRoot d.potential x *ᵥ (fun a => pullbackRawGradient d f a x)) i = _
  rw [hF, Matrix.mulVec_mulVec, canonicalMetricRoot_mul_hessian_at hp.1]
  rfl

theorem pullback_raw_metric_gradient_memLp_top (d : SourceData μ)
    {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin n) :
    MemLp (rawCanonicalMetricDerivative d.potential (pullbackRawGradient d f) i) ∞
      (potentialMeasure d.potential) := by
  have hg (a : Fin n) : MemLp (fun x => gradient f (gradient d.potential x) a) ∞
      (potentialMeasure d.potential) :=
    d.continuous_comp_gradient_memLp
      ((EuclideanSpace.proj a).continuous.comp (continuous_gradient_of_contDiff hf)) ∞
  have hm : MemLp (fun x => ∑ a : Fin n, canonicalMetricUnroot d.potential x i a *
      gradient f (gradient d.potential x) a) ∞ (potentialMeasure d.potential) :=
    memLp_finsetSum Finset.univ fun a _ => (actualUnroot_entry_memLp_top d i a).mul (hg a)
  exact (memLp_congr_ae (pullback_raw_metric_gradient_ae d f i)).mpr hm

end KLSConstantImprovement.ActualSourcePullbackMetricGradient405
#print axioms KLSConstantImprovement.ActualSourcePullbackMetricGradient405.canonicalMetricRoot_mul_hessian_at
#print axioms KLSConstantImprovement.ActualSourcePullbackMetricGradient405.pullback_raw_metric_gradient_ae
#print axioms KLSConstantImprovement.ActualSourcePullbackMetricGradient405.pullback_raw_metric_gradient_memLp_top

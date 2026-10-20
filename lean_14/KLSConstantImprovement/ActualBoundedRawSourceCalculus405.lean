import KLSConstantImprovement.ActualBoundedRawTestAlgebra405
import KLSConstantImprovement.ActualSourceGradientCoefficientPassage405
import KLS.WeakWeightedMean

/-! The bounded genuine weak test algebra also has global ordinary
derivative domains and the actual source Stein identity. The actual
target-coordinate pullbacks belong to this algebra, so finite products
in X and H are legitimate global weak source and Hessian tests. -/
noncomputable section
open MeasureTheory Matrix Filter Set
open scoped BigOperators ContDiff ENNReal
namespace KLSConstantImprovement.ActualBoundedRawSourceCalculus405
open KLS ActualBoundedCanonicalSource ActualCompactRawMetricGraph
open ActualCanonicalMetricEnergyGraph
open ActualWeakCanonicalMetricCore ActualWeakCanonicalMetricOrdinaryGraph
open ActualBoundedRawTestAlgebra405 ActualSourceLimitFluxDomains405
open ActualSourceGradientCoefficientPassage405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem canonicalMetricRoot_mul_hessian_at {φ : Space n → ℝ} {x : Space n}
    (hp : (coordinateHessian φ x).PosDef) :
    canonicalMetricRoot φ x * coordinateHessian φ x = canonicalMetricUnroot φ x := by
  have he := congrArg Matrix.transpose (hessian_mul_canonicalMetricRoot_at hp)
  have hR : (canonicalMetricRoot φ x).IsSymm := inverseSqrtMatrix_isSymm _
  have hS : (canonicalMetricUnroot φ x).IsSymm := hR.inv
  simpa only [Matrix.transpose_mul, hp.isHermitian.isSymm.eq, hR.eq, hS.eq] using he

namespace BoundedRawTest
variable {d : SourceData μ}

theorem ordinary_derivative_memLp (f : BoundedRawTest d) (i : Fin n) :
    MemLp (f.derivative i) 2 (potentialMeasure d.potential) := by
  have hm : MemLp (fun x => ∑ a, canonicalMetricUnroot d.potential x i a *
      rawCanonicalMetricDerivative d.potential f.derivative a x) 2
      (potentialMeasure d.potential) :=
    memLp_finsetSum Finset.univ fun a _ =>
      (actualUnroot_entry_memLp_top d i a).mul (f.metric_gradient a)
  apply (memLp_congr_ae ?_).mp hm
  filter_upwards [d.hessian_ae_source] with x hx
  have he : canonicalMetricUnroot d.potential x *ᵥ
      (canonicalMetricRoot d.potential x *ᵥ (fun a => f.derivative a x)) =
      (fun a => f.derivative a x) := by
    rw [Matrix.mulVec_mulVec, canonicalMetricUnroot_mul_root_at hx.1, Matrix.one_mulVec]
  exact congrFun he i

theorem global_source_stein (f : BoundedRawTest d) (i : Fin n) :
    (∫ x, f.derivative i x ∂potentialMeasure d.potential) =
      ∫ x, f.value x * gradient d.potential x i ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hX : MemLp (fun x => gradient d.potential x i) 2 (potentialMeasure d.potential) :=
    d.continuous_comp_gradient_memLp (EuclideanSpace.proj i).continuous 2
  have hfi : MemLp f.value 2 (potentialMeasure d.potential) :=
    f.value_top.mono_exponent (by simp)
  have hp := hfi.integrable_mul hX
  change Integrable (fun x => f.value x * gradient d.potential x i)
    (potentialMeasure d.potential) at hp
  simpa only [coordinateDerivative_eq_gradient] using
    integral_raw_derivative_potential d.source_C1 (f.weak_derivative i)
      (hfi.integrable (by simp)) ((ordinary_derivative_memLp f i).integrable (by simp))
      (by simpa only [coordinateDerivative_eq_gradient] using hp)

def coordinate (d : SourceData μ) (i : Fin n) : BoundedRawTest d where
  value := fun x => gradient d.potential x i
  derivative := fun a x => coordinateHessian d.potential x a i
  measurable := ((EuclideanSpace.proj i).continuous.comp d.gradient_lipschitz.continuous).aestronglyMeasurable
  bounded := ⟨d.sourceLipschitzConstant, fun x =>
    (PiLp.norm_apply_le (gradient d.potential x) i).trans
      (norm_gradient_le_of_lipschitz d.source_lipschitz x)⟩
  derivative_local := fun a E hE =>
    KLS.MemLp.restrict_volume_of_potentialMeasure (d.hessian_entry_memLp a i 2)
      d.source_C1.continuous hE
  weak_derivative := fun a => by
    have he : coordinateDerivative d.potential i = fun x => gradient d.potential x i :=
      funext fun x => coordinateDerivative_eq_gradient d.potential i x
    rw [← he]
    exact actual_hessian_hasLocalWeakCoordinateDerivative d.gradient_lipschitz.locallyLipschitz a i
  metric_gradient := by
    intro r
    letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
    have hm : MemLp (fun x => canonicalMetricUnroot d.potential x r i) 2
        (potentialMeasure d.potential) :=
      (actualUnroot_entry_memLp_top d r i).mono_exponent (by simp)
    apply (memLp_congr_ae ?_).mp hm
    filter_upwards [d.hessian_ae_source] with x hx
    change canonicalMetricUnroot d.potential x r i =
      (canonicalMetricRoot d.potential x * coordinateHessian d.potential x) r i
    rw [canonicalMetricRoot_mul_hessian_at hx.1]

end BoundedRawTest
end KLSConstantImprovement.ActualBoundedRawSourceCalculus405
#print axioms KLSConstantImprovement.ActualBoundedRawSourceCalculus405.canonicalMetricRoot_mul_hessian_at
#print axioms KLSConstantImprovement.ActualBoundedRawSourceCalculus405.BoundedRawTest.ordinary_derivative_memLp
#print axioms KLSConstantImprovement.ActualBoundedRawSourceCalculus405.BoundedRawTest.global_source_stein
#print axioms KLSConstantImprovement.ActualBoundedRawSourceCalculus405.BoundedRawTest.coordinate

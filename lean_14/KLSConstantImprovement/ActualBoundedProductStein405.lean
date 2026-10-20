import KLSConstantImprovement.ActualGlobalProductStein405

/-! A global source Stein product for a genuine ordinary H1 field and
an actual bounded raw test. The derivative product only needs L1. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualBoundedProductStein405
open KLS ActualBoundedCanonicalSource ActualBoundedRawTestAlgebra405 ActualBoundedRawSourceCalculus405
variable {n : ℕ} {μ : Measure (Space n)}
set_option backward.isDefEq.respectTransparency false

theorem actual_global_bounded_product_stein (d : SourceData μ) (f : BoundedRawTest d)
    {p : Space n → ℝ} {Dp : Fin n → Space n → ℝ}
    (hp : MemLp p 2 (potentialMeasure d.potential))
    (hDp : ∀ a, MemLp (Dp a) 2 (potentialMeasure d.potential))
    (hw : ∀ a, HasLocalWeakCoordinateDerivative p (Dp a) a) (a : Fin n) :
    (∫ x, gradient d.potential x a * f.value x * p x ∂potentialMeasure d.potential) =
      (∫ x, f.derivative a x * p x ∂potentialMeasure d.potential) +
        ∫ x, f.value x * Dp a x ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hpLoc (E : Set (Space n)) (hE : IsCompact E) : MemLp p 2 (volume.restrict E) :=
    KLS.MemLp.restrict_volume_of_potentialMeasure hp d.source_C1.continuous hE
  have hdLoc (b : Fin n) (E : Set (Space n)) (hE : IsCompact E) : MemLp (Dp b) 2 (volume.restrict E) :=
    KLS.MemLp.restrict_volume_of_potentialMeasure (hDp b) d.source_C1.continuous hE
  have hweak : HasLocalWeakCoordinateDerivative (fun x => f.value x * p x)
      (fun x => f.derivative a x * p x + f.value x * Dp a x) a :=
    (f.weak_derivative a).mul (hw a) f.value_local hpLoc (f.derivative_local a) (hdLoc a)
  have hfp : MemLp (fun x => f.value x * p x) 2 (potentialMeasure d.potential) := f.value_top.mul hp
  have hleft : Integrable (fun x => f.derivative a x * p x) (potentialMeasure d.potential) :=
    (ActualBoundedRawSourceCalculus405.BoundedRawTest.ordinary_derivative_memLp f a).integrable_mul hp
  have hright : MemLp (fun x => f.value x * Dp a x) 2 (potentialMeasure d.potential) := f.value_top.mul (hDp a)
  have hprod : Integrable (fun x => (f.value x * p x) * coordinateDerivative d.potential a x)
      (potentialMeasure d.potential) := by
    have hX : MemLp (fun x => gradient d.potential x a) 2 (potentialMeasure d.potential) :=
      d.continuous_comp_gradient_memLp (EuclideanSpace.proj a).continuous 2
    have hxp : Integrable (fun x => (f.value x * p x) * gradient d.potential x a)
        (potentialMeasure d.potential) := hfp.integrable_mul hX
    simpa only [coordinateDerivative_eq_gradient] using hxp
  have hs := integral_raw_derivative_potential d.source_C1 hweak (hfp.integrable (by norm_num))
    (hleft.add (hright.integrable (by norm_num))) hprod
  rw [integral_add hleft (hright.integrable (by norm_num))] at hs
  calc
    _ = ∫ x, (f.value x * p x) * coordinateDerivative d.potential a x ∂potentialMeasure d.potential := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change gradient d.potential x a * f.value x * p x = (f.value x * p x) * coordinateDerivative d.potential a x
        rw [coordinateDerivative_eq_gradient]
        ring
    _ = _ := hs.symm

end KLSConstantImprovement.ActualBoundedProductStein405
#print axioms KLSConstantImprovement.ActualBoundedProductStein405.actual_global_bounded_product_stein

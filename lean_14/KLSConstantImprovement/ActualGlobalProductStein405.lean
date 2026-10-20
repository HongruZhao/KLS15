import KLSConstantImprovement.ActualBoundedRawSourceCalculus405

/-! A global source Stein product identity for a genuine raw weak H1
field and the actual bounded target coordinate. All product and boundary
integrability is proved from the displayed scalar L2 domains. -/
noncomputable section
open MeasureTheory Matrix Set Filter
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualGlobalProductStein405
open KLS ActualBoundedCanonicalSource ActualBoundedRawTestAlgebra405
open ActualBoundedRawSourceCalculus405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_global_coordinate_product_stein (d : SourceData μ)
    {p : Space n → ℝ} {Dp : Fin n → Space n → ℝ}
    (hp : MemLp p 2 (potentialMeasure d.potential))
    (hDp : ∀ a, MemLp (Dp a) 2 (potentialMeasure d.potential))
    (hw : ∀ a, HasLocalWeakCoordinateDerivative p (Dp a) a) (j k : Fin n) :
    (∫ x, gradient d.potential x j * gradient d.potential x k * p x
      ∂potentialMeasure d.potential) =
      (∫ x, coordinateHessian d.potential x j k * p x ∂potentialMeasure d.potential) +
        ∫ x, gradient d.potential x k * Dp j x ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let X := BoundedRawTest.coordinate d k
  have hpLoc (E : Set (Space n)) (hE : IsCompact E) : MemLp p 2 (volume.restrict E) :=
    KLS.MemLp.restrict_volume_of_potentialMeasure hp d.source_C1.continuous hE
  have hdLoc (a : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (Dp a) 2 (volume.restrict E) :=
    KLS.MemLp.restrict_volume_of_potentialMeasure (hDp a) d.source_C1.continuous hE
  have hweak : HasLocalWeakCoordinateDerivative (fun x => gradient d.potential x k * p x)
      (fun x => coordinateHessian d.potential x j k * p x + gradient d.potential x k * Dp j x) j :=
    (X.weak_derivative j).mul (hw j) X.value_local hpLoc (X.derivative_local j) (hdLoc j)
  have hX : MemLp (fun x => gradient d.potential x k) ∞ (potentialMeasure d.potential) := X.value_top
  have hf : MemLp (fun x => gradient d.potential x k * p x) 2 (potentialMeasure d.potential) := hX.mul hp
  have hleft : MemLp (fun x => coordinateHessian d.potential x j k * p x) 2
      (potentialMeasure d.potential) := (d.hessian_entry_memLp j k ∞).mul hp
  have hright : MemLp (fun x => gradient d.potential x k * Dp j x) 2
      (potentialMeasure d.potential) := hX.mul (hDp j)
  have hF : MemLp (fun x => coordinateHessian d.potential x j k * p x +
      gradient d.potential x k * Dp j x) 2 (potentialMeasure d.potential) := hleft.add hright
  have hXj : MemLp (fun x => gradient d.potential x j) 2 (potentialMeasure d.potential) :=
    d.continuous_comp_gradient_memLp (EuclideanSpace.proj j).continuous 2
  have hprod : Integrable (fun x => (gradient d.potential x k * p x) *
      coordinateDerivative d.potential j x) (potentialMeasure d.potential) := by
    have hh : Integrable (fun x => (gradient d.potential x k * p x) *
        gradient d.potential x j) (potentialMeasure d.potential) := hf.integrable_mul hXj
    simpa only [coordinateDerivative_eq_gradient] using hh
  have hs := integral_raw_derivative_potential d.source_C1 hweak
    (hf.integrable (by norm_num)) (hF.integrable (by norm_num)) hprod
  have hLi : Integrable (fun x => coordinateHessian d.potential x j k * p x)
      (potentialMeasure d.potential) := hleft.integrable (by norm_num)
  have hRi : Integrable (fun x => gradient d.potential x k * Dp j x)
      (potentialMeasure d.potential) := hright.integrable (by norm_num)
  rw [integral_add hLi hRi] at hs
  calc
    _ = ∫ x, (gradient d.potential x k * p x) * coordinateDerivative d.potential j x
        ∂potentialMeasure d.potential := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change gradient d.potential x j * gradient d.potential x k * p x =
          (gradient d.potential x k * p x) * coordinateDerivative d.potential j x
        rw [coordinateDerivative_eq_gradient]
        ring
    _ = _ := hs.symm

end KLSConstantImprovement.ActualGlobalProductStein405
#print axioms KLSConstantImprovement.ActualGlobalProductStein405.actual_global_coordinate_product_stein

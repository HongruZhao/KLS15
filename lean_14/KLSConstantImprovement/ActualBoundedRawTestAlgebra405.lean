import KLSConstantImprovement.ActualSourceGlobalRawHessianEvolution405
import KLSConstantImprovement.ActualSourceTensorGramMetricBinding

/-! Bounded genuine weak scalar tests form an algebra on the actual
source. In particular every finite polynomial in the actual Hessian
entries is a valid global Hessian-PDE test. Only weak differentiation
and literal metric L2 domains are used; there is no classical derivative
of the C1,1 Hessian. -/
noncomputable section
open MeasureTheory Matrix Set Filter
open scoped BigOperators ContDiff Topology ENNReal
namespace KLSConstantImprovement.ActualBoundedRawTestAlgebra405
open KLS ActualBoundedCanonicalSource ActualCompactRawMetricGraph
open ActualSourceHessianEvolution405 ActualSourceGlobalRawHessianEvolution405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

structure BoundedRawTest (d : SourceData μ) where
  value : Space n → ℝ
  derivative : Fin n → Space n → ℝ
  measurable : AEStronglyMeasurable value (potentialMeasure d.potential)
  bounded : ∃ B : ℝ, ∀ x, ‖value x‖ ≤ B
  derivative_local : ∀ a E, IsCompact E → MemLp (derivative a) 2 (volume.restrict E)
  weak_derivative : ∀ a, HasLocalWeakCoordinateDerivative value (derivative a) a
  metric_gradient : ∀ r, MemLp (rawCanonicalMetricDerivative d.potential derivative r) 2
    (potentialMeasure d.potential)

namespace BoundedRawTest
variable {d : SourceData μ}

theorem value_top (f : BoundedRawTest d) : MemLp f.value ∞ (potentialMeasure d.potential) := by
  obtain ⟨B, hb⟩ := f.bounded
  exact memLp_top_of_bound f.measurable B (Eventually.of_forall hb)

theorem value_local (f : BoundedRawTest d) (E : Set (Space n)) (hE : IsCompact E) :
    MemLp f.value 2 (volume.restrict E) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  exact KLS.MemLp.restrict_volume_of_potentialMeasure
    (f.value_top.mono_exponent (by simp)) d.source_C1.continuous hE

theorem value_local_top (f : BoundedRawTest d) (E : Set (Space n)) (hE : IsCompact E) :
    MemLp f.value ∞ (volume.restrict E) :=
  KLS.MemLp.restrict_volume_of_potentialMeasure f.value_top d.source_C1.continuous hE

def const (d : SourceData μ) (c : ℝ) : BoundedRawTest d where
  value := fun _ => c
  derivative := fun _ _ => 0
  measurable := aestronglyMeasurable_const
  bounded := ⟨‖c‖, fun _ => le_rfl⟩
  derivative_local := fun _ _ _ => MemLp.zero
  weak_derivative := hasLocalWeakCoordinateDerivative_const c
  metric_gradient := by
    intro r
    have he : rawCanonicalMetricDerivative d.potential (fun (_ : Fin n) (_ : Space n) => (0 : ℝ)) r =
        (0 : Space n → ℝ) := by
      funext x
      simp only [rawCanonicalMetricDerivative, mul_zero, Finset.sum_const_zero, Pi.zero_apply]
    rw [he]
    exact MemLp.zero

def add (f g : BoundedRawTest d) : BoundedRawTest d where
  value := fun x => f.value x + g.value x
  derivative := fun a x => f.derivative a x + g.derivative a x
  measurable := f.measurable.add g.measurable
  bounded := by
    obtain ⟨B, hB⟩ := f.bounded
    obtain ⟨C, hC⟩ := g.bounded
    exact ⟨B+C, fun x => (norm_add_le _ _).trans (add_le_add (hB x) (hC x))⟩
  derivative_local := fun a E hE => (f.derivative_local a E hE).add (g.derivative_local a E hE)
  weak_derivative := fun a => (f.weak_derivative a).add (g.weak_derivative a)
    (locallyIntegrable_of_memLp_two_on_compacts f.value_local)
    (locallyIntegrable_of_memLp_two_on_compacts g.value_local)
    (locallyIntegrable_of_memLp_two_on_compacts (f.derivative_local a))
    (locallyIntegrable_of_memLp_two_on_compacts (g.derivative_local a))
  metric_gradient := by
    intro r
    have he : rawCanonicalMetricDerivative d.potential
        (fun a x => f.derivative a x + g.derivative a x) r = fun x =>
          rawCanonicalMetricDerivative d.potential f.derivative r x +
            rawCanonicalMetricDerivative d.potential g.derivative r x := by
      funext x
      simp only [rawCanonicalMetricDerivative, mul_add, Finset.sum_add_distrib]
    rw [he]
    exact (f.metric_gradient r).add (g.metric_gradient r)

def mul (f g : BoundedRawTest d) : BoundedRawTest d where
  value := fun x => f.value x * g.value x
  derivative := fun a x => f.derivative a x * g.value x + f.value x * g.derivative a x
  measurable := f.measurable.mul g.measurable
  bounded := by
    obtain ⟨B, hB⟩ := f.bounded
    obtain ⟨C, hC⟩ := g.bounded
    have hB0 : 0 ≤ B := (norm_nonneg (f.value 0)).trans (hB 0)
    exact ⟨B*C, fun x => by
      rw [norm_mul]
      exact mul_le_mul (hB x) (hC x) (norm_nonneg _) hB0⟩
  derivative_local := by
    intro a E hE
    have hfirst : MemLp (fun x => f.derivative a x * g.value x) 2 (volume.restrict E) := by
      have hm : MemLp (fun x => g.value x * f.derivative a x) 2 (volume.restrict E) :=
        (g.value_local_top E hE).mul (f.derivative_local a E hE)
      exact (memLp_congr_ae (Eventually.of_forall fun x => mul_comm _ _)).mp hm
    exact hfirst.add ((f.value_local_top E hE).mul (g.derivative_local a E hE))
  weak_derivative := fun a => (f.weak_derivative a).mul (g.weak_derivative a)
    f.value_local g.value_local (f.derivative_local a) (g.derivative_local a)
  metric_gradient := by
    intro r
    have he : rawCanonicalMetricDerivative d.potential
        (fun a x => f.derivative a x * g.value x + f.value x * g.derivative a x) r =
      fun x => g.value x * rawCanonicalMetricDerivative d.potential f.derivative r x +
        f.value x * rawCanonicalMetricDerivative d.potential g.derivative r x := by
      funext x
      simp only [rawCanonicalMetricDerivative, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro a _ <;> ring
    rw [he]
    exact (g.value_top.mul (f.metric_gradient r)).add (f.value_top.mul (g.metric_gradient r))

def hessian (d : SourceData μ) (i j : Fin n) : BoundedRawTest d where
  value := fun x => coordinateHessian d.potential x i j
  derivative := fun a x => d.third x a i j
  measurable := (d.hessian_entry_memLp i j 2).aestronglyMeasurable
  bounded := ⟨16 / d.targetConvexityConstant, fun x =>
    coordinateHessian_entry_bound_of_gradient_lipschitz d.gradient_lipschitz x i j⟩
  derivative_local := fun a E hE => d.third_local_L2 a i j E hE
  weak_derivative := fun a => d.third_weak_derivative a i j
  metric_gradient := d.hessian_entry_raw_metric_memLp i j

theorem global_hessian_test (f : BoundedRawTest d) (i j : Fin n) :
    (∫ x, ∑ r,
      rawCanonicalMetricDerivative d.potential (fun a y => d.third y a i j) r x *
        rawCanonicalMetricDerivative d.potential f.derivative r x ∂potentialMeasure d.potential) =
      ∫ x, (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) *
        f.value x ∂potentialMeasure d.potential := by
  obtain ⟨B, hb⟩ := f.bounded
  exact actual_global_bounded_raw_hessian_evolution d f.measurable hb
    f.derivative_local f.weak_derivative f.metric_gradient i j

end BoundedRawTest
end KLSConstantImprovement.ActualBoundedRawTestAlgebra405
#print axioms KLSConstantImprovement.ActualBoundedRawTestAlgebra405.BoundedRawTest.add
#print axioms KLSConstantImprovement.ActualBoundedRawTestAlgebra405.BoundedRawTest.mul
#print axioms KLSConstantImprovement.ActualBoundedRawTestAlgebra405.BoundedRawTest.hessian
#print axioms KLSConstantImprovement.ActualBoundedRawTestAlgebra405.BoundedRawTest.global_hessian_test

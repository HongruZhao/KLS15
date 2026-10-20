import KLSConstantImprovement.ActualBoundedRawTestAlgebra405

/-! A genuine local weak algebra. It asserts no global source form
membership: values are locally bounded and raw derivatives locally L2. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualLocalBoundedWeakAlgebra405
open KLS ActualBoundedCanonicalSource ActualBoundedRawTestAlgebra405
variable {n : ℕ} {μ : Measure (Space n)}
set_option backward.isDefEq.respectTransparency false

structure LocalRawTest (n : ℕ) where
  value : Space n → ℝ
  derivative : Fin n → Space n → ℝ
  value_local_top : ∀ E, IsCompact E → MemLp value ∞ (volume.restrict E)
  derivative_local : ∀ a E, IsCompact E → MemLp (derivative a) 2 (volume.restrict E)
  weak_derivative : ∀ a, HasLocalWeakCoordinateDerivative value (derivative a) a

namespace LocalRawTest

theorem value_local (f : LocalRawTest n) (E : Set (Space n)) (hE : IsCompact E) :
    MemLp f.value 2 (volume.restrict E) := by
  letI : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hE.measure_ne_top
  exact (f.value_local_top E hE).mono_exponent (by simp)

def mul (f g : LocalRawTest n) : LocalRawTest n where
  value := fun x => f.value x * g.value x
  derivative := fun a x => f.derivative a x * g.value x + f.value x * g.derivative a x
  value_local_top := fun E hE => (f.value_local_top E hE).mul (g.value_local_top E hE)
  derivative_local := by
    intro a E hE
    have hfirst : MemLp (fun x => f.derivative a x * g.value x) 2 (volume.restrict E) := by
      have hm : MemLp (fun x => g.value x * f.derivative a x) 2 (volume.restrict E) :=
        (g.value_local_top E hE).mul (f.derivative_local a E hE)
      exact (memLp_congr_ae (Eventually.of_forall fun x => mul_comm _ _)).mp hm
    exact hfirst.add ((f.value_local_top E hE).mul (g.derivative_local a E hE))
  weak_derivative := fun a => (f.weak_derivative a).mul (g.weak_derivative a)
    f.value_local g.value_local (f.derivative_local a) (g.derivative_local a)

def ofBoundedRawTest {d : SourceData μ} (f : BoundedRawTest d) : LocalRawTest n where
  value := f.value
  derivative := f.derivative
  value_local_top := f.value_local_top
  derivative_local := f.derivative_local
  weak_derivative := f.weak_derivative

end LocalRawTest

def localRawTestSum {ι : Type*} [Fintype ι] (f : ι → LocalRawTest n) : LocalRawTest n where
  value := fun x => ∑ i, (f i).value x
  derivative := fun a x => ∑ i, (f i).derivative a x
  value_local_top := fun E hE => memLp_finsetSum Finset.univ fun i _ => (f i).value_local_top E hE
  derivative_local := fun a E hE => memLp_finsetSum Finset.univ fun i _ => (f i).derivative_local a E hE
  weak_derivative := fun a => hasLocalWeakCoordinateDerivative_finset_sum Finset.univ
    (fun i _ => (f i).weak_derivative a)
    (fun i _ => locallyIntegrable_of_memLp_two_on_compacts (f i).value_local)
    (fun i _ => locallyIntegrable_of_memLp_two_on_compacts ((f i).derivative_local a))

end KLSConstantImprovement.ActualLocalBoundedWeakAlgebra405

#print axioms KLSConstantImprovement.ActualLocalBoundedWeakAlgebra405.LocalRawTest.mul
#print axioms KLSConstantImprovement.ActualLocalBoundedWeakAlgebra405.localRawTestSum

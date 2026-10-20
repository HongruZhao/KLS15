import KLS.SecondTaylorQuadraticEquivalence
import KLS.FullQuadraticVarianceBound
import KLS.WeightedL2TaylorTensor

/-! An unconditional actual-law quadratic observation bound, directly reused
from the released elliptic quadratic-eight theorem. It is a bound for the
literal normalized tilt Taylor coefficient. Identifying this map with the
adjoint of the new paper's `J L` remains a separate obligation. -/

open MeasureTheory Set InnerProductSpace
open scoped ContDiff BigOperators RealInnerProductSpace

noncomputable section
namespace KLS.DeterministicBridge

variable {n : ℕ} {V : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure V)]

/-- The constant two includes the exact factorial and all ordered tensor
coordinates. There is no unproved quadratic estimate among the hypotheses. -/
theorem quadratic_observation_le_two
    (hV : ContDiff ℝ 2 V) (hκ : 0 < κ)
    (hstrong : StrongConvexOn univ κ V)
    (hiso : IsIsotropic (potentialMeasure V))
    (f : Lp ℝ 2 (potentialMeasure V)) :
    (∑ a : Fin 2 → Fin n, exponentialTiltCoordinateTaylor V f 2 a ^ 2) ≤
      2 * ‖f‖ ^ 2 := by
  have hadm : admissibleMeasure (potentialMeasure V) :=
    ⟨inferInstance, measureLogConcave_potentialMeasure hV.continuous.measurable
      (convexOn_of_strongConvexOn_nonneg hκ.le hstrong), hiso⟩
  exact hadm.quadraticVarianceEight_unconditional.secondTaylor_norm_bound
    hV hκ hstrong hiso f

/-- The actual quadratic observation bound lifts to every finite family with
the genuine Hilbert sum norm, without changing the constant. -/
theorem quadratic_observation_finite_family_le_two
    (hV : ContDiff ℝ 2 V) (hκ : 0 < κ)
    (hstrong : StrongConvexOn univ κ V)
    (hiso : IsIsotropic (potentialMeasure V))
    {ι : Type*} [Fintype ι] (g : CenteredL2.Family (potentialMeasure V) ι) :
    ‖weightedL2TaylorTensor V 2 g‖ ^ 2 ≤ 2 * ‖g‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  change (∑ a : Fin 2 → Fin n, ∑ i : ι,
      exponentialTiltCoordinateTaylor V (g i) 2 a ^ 2) ≤ 2 * ‖g‖ ^ 2
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ i : ι, 2 * ‖g i‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => quadratic_observation_le_two hV hκ hstrong hiso (g i)
    _ = _ := by rw [← Finset.mul_sum, PiLp.norm_sq_eq_of_L2]

end KLS.DeterministicBridge
end

#print axioms KLS.DeterministicBridge.quadratic_observation_le_two
#print axioms KLS.DeterministicBridge.quadratic_observation_finite_family_le_two

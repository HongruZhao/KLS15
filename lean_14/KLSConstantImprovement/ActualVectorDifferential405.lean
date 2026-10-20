import KLSConstantImprovement.ActualVectorL2Composition405
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.MeanValue

/-! Coordinate formulas for genuine multivariate composition. Global
Lipschitz continuity bounds the partial derivatives without a hypothesis
on the Lipschitz continuity of those derivatives. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ContDiff Topology NNReal ENNReal
namespace KLSConstantImprovement.ActualVectorDifferential405
open KLS
variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def vectorPartial (η : (ι → ℝ) → ℝ) (j : ι) (v : ι → ℝ) : ℝ :=
  fderiv ℝ η v (Pi.single j 1)

theorem vectorPartial_continuous {η : (ι → ℝ) → ℝ}
    (hη : ContDiff ℝ 1 η) (j : ι) : Continuous (vectorPartial η j) := by
  exact (hη.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem vectorPartial_bound {η : (ι → ℝ) → ℝ} {L : ℝ≥0}
    (hLip : LipschitzWith L η) (j : ι) (v : ι → ℝ) : ‖vectorPartial η j v‖ ≤ L := by
  calc
    _ ≤ ‖fderiv ℝ η v‖ * ‖Pi.single j (1 : ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ η v‖ := by rw [Pi.norm_single, norm_one, mul_one]
    _ ≤ _ := norm_fderiv_le_of_lipschitz ℝ hLip

theorem fderiv_eq_sum_vectorPartial (η : (ι → ℝ) → ℝ) (v w : ι → ℝ) :
    fderiv ℝ η v w = ∑ j, vectorPartial η j v * w j := by
  have hw : w = ∑ j, w j • Pi.single j (1 : ℝ) := by
    ext j
    simp [Pi.single_apply, eq_comm]
  calc
    _ = fderiv ℝ η v (∑ j, w j • Pi.single j (1 : ℝ)) := congrArg (fderiv ℝ η v) hw
    _ = ∑ j, w j * fderiv ℝ η v (Pi.single j (1 : ℝ)) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = _ := Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem coordinateDerivative_vector_comp {η : (ι → ℝ) → ℝ}
    (hη : ContDiff ℝ 1 η) {f : ι → Space n → ℝ}
    (hf : ∀ j, ContDiff ℝ 1 (f j)) (i : Fin n) (x : Space n) :
    coordinateDerivative (fun y => η (fun j => f j y)) i x =
      ∑ j, vectorPartial η j (fun a => f a x) * coordinateDerivative (f j) i x := by
  have hv : ContDiff ℝ 1 (fun y j => f j y) := contDiff_pi.mpr hf
  change (fderiv ℝ (η ∘ (fun y j => f j y)) x) (EuclideanSpace.single i 1) = _
  rw [fderiv_comp x (hη.differentiable one_ne_zero _) (hv.differentiable one_ne_zero _),
    ContinuousLinearMap.comp_apply, fderiv_pi (fun j => (hf j).differentiable one_ne_zero x)]
  change fderiv ℝ η (fun j => f j x) (fun j => coordinateDerivative (f j) i x) = _
  exact fderiv_eq_sum_vectorPartial η _ _

end KLSConstantImprovement.ActualVectorDifferential405

#print axioms KLSConstantImprovement.ActualVectorDifferential405.vectorPartial_continuous
#print axioms KLSConstantImprovement.ActualVectorDifferential405.vectorPartial_bound
#print axioms KLSConstantImprovement.ActualVectorDifferential405.coordinateDerivative_vector_comp

import KLSConstantImprovement.ActualSourceDirectCubicBalance405
import KLSConstantImprovement.ActualDeficitTensorBounds

/-! The direct cubic moment is the literal ordered tensor square after
actual H^(1/2) whitening in all three slots. No Hilbert--Schmidt norm is
asserted invariant under this nonorthogonal transformation. -/
noncomputable section
open Matrix MeasureTheory Filter
open scoped BigOperators MatrixOrder
namespace KLSConstantImprovement.ActualDirectCubicMomentBinding405
open KLS ActualBoundedCanonicalSource ActualQuarticCongruence405
open ActualQuarticWhiteFrame405 ActualQuarticThirdWhitening405 ActualFullTensorWhitening
open ActualDirectCubicWhitening405 ActualDeficitTensorBounds ActualSourceQuarticBinding405
open ActualSourceDirectCubicBalance405
variable {n : ℕ} {μ : Measure (Space n)}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem direct_white_tensor_square (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.IsSymm)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    tensorSquare (whiteThirdSlice Q T) = ((Q * Q) * rawGram (Q * Q) T).trace := by
  rw [tensorSquare_eq_sum_slices]
  calc
    _ = ∑ i, (whiteThirdSlice Q T i * whiteThirdSlice Q T i).trace :=
      Finset.sum_congr rfl fun i _ => matrixFrobeniusSq_eq_trace_sq (whiteThirdSlice_symmetric Q hQ T hT i)
    _ = (whiteGram (whiteThirdSlice Q T)).trace := rfl
    _ = (Q * rawGram (Q * Q) T * Q).trace := by rw [whiteGram_whiteThirdSlice Q hQ]
    _ = _ := Matrix.trace_mul_cycle _ _ _

theorem direct_cubic_moment_eq_tensor_square (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosSemidef) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT : ∀ i, (T i).IsSymm) :
    (H * matrixTraceGram H T).trace = tensorSquare (threeSlotAction (CFC.sqrt H) T) := by
  have hQ : (CFC.sqrt H).IsSymm := (CFC.sqrt_nonneg H).posSemidef.isHermitian.isSymm
  have hsq : CFC.sqrt H * CFC.sqrt H = H := CFC.sqrt_mul_sqrt_self H hH.nonneg
  have he := direct_white_tensor_square (CFC.sqrt H) hQ T hT
  rw [hsq, rawGram_eq_matrixTraceGram] at he
  have hA : whiteThirdSlice (CFC.sqrt H) T = threeSlotAction (CFC.sqrt H) T := by
    funext i j k
    exact whiteThirdSlice_eq_threeSlot _ hQ T i j k
  rw [hA] at he
  exact he.symm

theorem actual_direct_moment_tensor_binding (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      actualDirectMoment d T x = tensorSquare (threeSlotAction (CFC.sqrt (coordinateHessian d.potential x)) T) := by
  filter_upwards [d.hessian_ae_source] with x hx
  exact direct_cubic_moment_eq_tensor_square _ hx.1.posSemidef T hT

theorem actual_direct_white_tensor_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    Integrable (fun x => tensorSquare (threeSlotAction (CFC.sqrt (coordinateHessian d.potential x)) T))
      (potentialMeasure d.potential) :=
  (actual_direct_moment_integrable d T).congr (actual_direct_moment_tensor_binding d T hT)

end KLSConstantImprovement.ActualDirectCubicMomentBinding405

#print axioms KLSConstantImprovement.ActualDirectCubicMomentBinding405.direct_cubic_moment_eq_tensor_square
#print axioms KLSConstantImprovement.ActualDirectCubicMomentBinding405.actual_direct_moment_tensor_binding
#print axioms KLSConstantImprovement.ActualDirectCubicMomentBinding405.actual_direct_white_tensor_integrable

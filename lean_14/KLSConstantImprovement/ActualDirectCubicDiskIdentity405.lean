import KLSConstantImprovement.ActualDirectDeficitBinding405
import KLSConstantImprovement.ActualSourceDirectCubicCharge405

/-! The exact direct deficit disk identity for the literal source and tensor.
The curvature and commutator terms are retained; no numerical deficit
or analytic domain hypothesis is supplied. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualDirectCubicDiskIdentity405
open KLS ActualBoundedCanonicalSource ActualSourceMeanGram405
open ActualSourceHessianEvolution405 ActualDirectCubicPointwise405
open ActualSourceDirectCubicEnergy405 ActualSourceDirectCubicBalance405
open ActualSourceDirectCubicCharge405 ActualSourceUnfilteredDeficit405
open ActualDirectDeficitBinding405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_direct_retained_disk_identity (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j) :
    (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) +
      2 * (∫ x, actualDirectTargetCurvature d T x ∂potentialMeasure d.potential) +
      (∫ x, directCubicCommutatorCharge (coordinateHessian d.potential x) T
        (sourceThirdMatrix d x) ∂potentialMeasure d.potential) +
      3 * actualMatrixBLCross d 1 T = 3 * (sourceMeanGram d T).trace := by
  have hb := actual_direct_cubic_primitive_identity d T
  have hc := actual_direct_integrated_commutator_identity d T hT12 hT23
  rw [actual_direct_unfiltered_deficit_identity d hiso T]
  linarith

theorem actual_direct_moment_le_mean_minus_cross (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j) :
    (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) ≤
      3 * ((sourceMeanGram d T).trace - actualMatrixBLCross d 1 T) := by
  have he := actual_direct_retained_disk_identity d hiso T hT12 hT23
  have hp := actual_direct_target_curvature_nonnegative d T
    (fun i => Matrix.IsSymm.ext fun j k => hT23 i k j)
  have hr := actual_direct_commutator_integral_nonnegative d T
  linarith

end KLSConstantImprovement.ActualDirectCubicDiskIdentity405
#print axioms KLSConstantImprovement.ActualDirectCubicDiskIdentity405.actual_direct_retained_disk_identity
#print axioms KLSConstantImprovement.ActualDirectCubicDiskIdentity405.actual_direct_moment_le_mean_minus_cross

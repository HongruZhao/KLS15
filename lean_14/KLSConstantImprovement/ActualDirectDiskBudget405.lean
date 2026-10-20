import KLSConstantImprovement.ActualMatchedDeficitLimit405
import KLSConstantImprovement.ActualDirectCubicDiskIdentity405
import KLSConstantImprovement.SourceMatchedMeanResponseConditionalPayoff

/-! Actual same-source scalar disk state and direct cubic budget. Every
number is a literal tensor norm, Gram mean or Hessian sandwich integral.
The positive curvature and commutator charges are retained. -/
noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators MatrixOrder
namespace KLSConstantImprovement.ActualDirectDiskBudget405
open KLS ActualBoundedCanonicalSource ActualSourceMeanGram405 ActualSourceMeanGramOrder405
open ActualSourceUnfilteredDeficit405 ActualMatchedDeficitLimit405 ActualCubicGramHalfBinding405
open ActualDeficitTensorBounds ActualSourceDirectCubicBalance405 ActualDirectCubicPointwise405
open ActualSourceHessianEvolution405 ActualDirectCubicDiskIdentity405
open SourceMatchedMeanResponseConditionalPayoff
variable {n : ℕ} {μ : Measure (Space n)}
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def actualMean (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (sourceMeanGram d T).trace

def actualGramHalfDeficit (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  2 * tensorSquare T - ∫ x, rawHessianTraceSquare (coordinateHessian d.potential x)
    (CFC.sqrt (sourceCoefficientGram T)) ∂potentialMeasure d.potential

def actualOrientationGap (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  2 * tensorSquare T - actualMean d T - actualGramHalfDeficit d T

def actualDiskRadiusTerm (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt (actualMean d T * actualGramHalfDeficit d T)

theorem actual_mean_trace_integral (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    actualMean d T = ∫ x, ∑ i,
      (T i * coordinateHessian d.potential x * T i * coordinateHessian d.potential x).trace
        ∂potentialMeasure d.potential := by
  change (∑ i, ∫ x, matrixTraceGram (coordinateHessian d.potential x) T i i
    ∂potentialMeasure d.potential) = _
  simp_rw [traceGram_cyclic]
  exact (integral_finsetSum Finset.univ fun i _ => d.signed_sandwich_integrable (T i)).symm

theorem actual_disk_nonnegative_and_budget (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j) :
    0 ≤ actualMean d T ∧ 0 ≤ actualGramHalfDeficit d T ∧
      actualGramHalfDeficit d T ≤ 2 * tensorSquare T - actualMean d T ∧
      0 ≤ actualOrientationGap d T ∧ 0 ≤ tensorSquare T - actualOrientationGap d T / 2 := by
  have hTs (i : Fin n) : (T i).IsSymm := Matrix.IsSymm.ext fun j k => hT23 i k j
  have hr : 0 ≤ actualMean d T := (actual_meanGram_posSemidef d T hTs).trace_nonneg
  have hb := actual_fullSymmetric_gram_half_deficit_budget d hiso T hT12 hT23
  change 0 ≤ actualGramHalfDeficit d T ∧ actualGramHalfDeficit d T ≤ _ at hb
  rw [← actual_mean_trace_integral] at hb
  refine ⟨hr, hb.1, hb.2, ?_, ?_⟩ <;> unfold actualOrientationGap <;> linarith

theorem actual_matched_scalar_disk (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j) :
    (actualMean d T - (tensorSquare T - actualOrientationGap d T / 2)) ^ 2 +
      actualDiskRadiusTerm d T ^ 2 = (tensorSquare T - actualOrientationGap d T / 2) ^ 2 := by
  obtain ⟨hr, hd, _, _, _⟩ := actual_disk_nonnegative_and_budget d hiso T hT12 hT23
  have hs := Real.sq_sqrt (mul_nonneg hr hd)
  unfold actualDiskRadiusTerm actualOrientationGap
  nlinarith

theorem actual_direct_retained_support (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j) :
    (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) +
      2 * (∫ x, actualDirectTargetCurvature d T x ∂potentialMeasure d.potential) +
      (∫ x, directCubicCommutatorCharge (coordinateHessian d.potential x) T
        (sourceThirdMatrix d x) ∂potentialMeasure d.potential) ≤
      3 * (actualMean d T + actualDiskRadiusTerm d T) := by
  have hc := actual_fullSymmetric_base_BL_cross_deficit_cap d hiso T hT12 hT23
  change actualMatrixBLCross d 1 T ^ 2 ≤ actualMean d T * actualGramHalfDeficit d T at hc
  obtain ⟨hr, hd, _, _, _⟩ := actual_disk_nonnegative_and_budget d hiso T hT12 hT23
  have hs : actualDiskRadiusTerm d T ^ 2 = actualMean d T * actualGramHalfDeficit d T :=
    Real.sq_sqrt (mul_nonneg hr hd)
  have hl : -actualMatrixBLCross d 1 T ≤ actualDiskRadiusTerm d T :=
    le_of_sq_le_sq (by nlinarith [hc]) (Real.sqrt_nonneg _)
  have he := actual_direct_retained_disk_identity d hiso T hT12 hT23
  change _ = 3 * actualMean d T at he
  linarith

theorem actual_direct_universal_constant (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j) :
    (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) +
      2 * (∫ x, actualDirectTargetCurvature d T x ∂potentialMeasure d.potential) +
      (∫ x, directCubicCommutatorCharge (coordinateHessian d.potential x) T
        (sourceThirdMatrix d x) ∂potentialMeasure d.potential) ≤
      3 * (1 + Real.sqrt 2) * (tensorSquare T - actualOrientationGap d T / 2) := by
  obtain ⟨_, _, _, _, hN⟩ := actual_disk_nonnegative_and_budget d hiso T hT12 hT23
  have hd := actual_matched_scalar_disk d hiso T hT12 hT23
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hc : (1 : ℝ)^2 + 1^2 ≤ ((1 + Real.sqrt 2) - 1)^2 := by nlinarith
  have hcap : 0 ≤ (1 + Real.sqrt (2 : ℝ)) - 1 := by
    simpa only [add_sub_cancel_left] using Real.sqrt_nonneg (2 : ℝ)
  have hl := disk_linear_support hN hcap hc (le_of_eq hd)
  have hp := actual_direct_retained_support d hiso T hT12 hT23
  nlinarith

end KLSConstantImprovement.ActualDirectDiskBudget405
#print axioms KLSConstantImprovement.ActualDirectDiskBudget405.actual_disk_nonnegative_and_budget
#print axioms KLSConstantImprovement.ActualDirectDiskBudget405.actual_matched_scalar_disk
#print axioms KLSConstantImprovement.ActualDirectDiskBudget405.actual_direct_retained_support
#print axioms KLSConstantImprovement.ActualDirectDiskBudget405.actual_direct_universal_constant

import KLSConstantImprovement.ActualResponseFullSymCoercivity405
import KLSConstantImprovement.ActualWeightedWhiteFamily405
import KLSConstantImprovement.CoupledCenterFinite

/-! Actual positive-metric row loss controls the same response center.
Finite statements only; original-law instantiation is a separate wrapper. -/
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder
namespace KLSConstantImprovement.CoupledCenterMetric
open KLS ActualWeightedWhiteFamily405 ActualFullSymmetricProduction
open ActualResponseProductionHalfSquare405 ActualResponseProductionAlgebra405
open ActualTensorRowWhite405 ActualQuarticThirdWhitening405 ActualQuarticWhiteFrame405
open ActualQuarticCongruence405 ActualFullSymmetricTensorOrdering
open ActualResponseCompletionWhitening405 ActualWhitenedJacobianEnergy405 ActualWhitenedJacobianSymmetry405
open MixedCubicRankSlicing FourthCubicProjectionDefect CoupledCenterFinite
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000

theorem metricWhiteFamily_error (H F : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef)
    (N T : Fin n → Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    metricWhiteFamily H (fun i => H⁻¹ * mixFamily F N i - c • (T i * H)) =
      fun i a b => firstAction ((inverseSqrtMatrix H)⁻¹ * F * (inverseSqrtMatrix H)⁻¹)
        (whiteThirdSlice (inverseSqrtMatrix H) N) i a b -
          c * whiteThirdSlice (inverseSqrtMatrix H)⁻¹ T i a b := by
  let R := inverseSqrtMatrix H
  let S := R⁻¹
  have hR : R.IsSymm := inverseSqrtMatrix_isSymm H
  have hS : S.IsSymm := hR.inv
  have hSS : S * S = H := by
    have he : S.transpose * S = H := inverseSqrtMatrix_inverse_gram hH
    simpa only [hS.eq] using he
  have hunit : IsUnit R.det := isUnit_iff_ne_zero.mpr (inverseSqrtMatrix_det_ne_zero_of_posDef hH)
  have hRS : R * S = 1 := Matrix.mul_nonsing_inv R hunit
  have hSR : S * R = 1 := Matrix.nonsing_inv_mul R hunit
  have hRR : R * R = H⁻¹ := by
    unfold R inverseSqrtMatrix
    rw [← Matrix.mul_inv_rev, CFC.sqrt_mul_sqrt_self H hH.posSemidef.nonneg]
  have hSJ : S * H⁻¹ = R := by rw [← hRR, ← Matrix.mul_assoc, hSR, Matrix.one_mul]
  have hHR : H * R = S := by rw [← hSS, Matrix.mul_assoc, hSR, Matrix.mul_one]
  have hw (i : Fin n) : whitenedJacobian H (H⁻¹ * mixFamily F N i - c • (T i * H)) =
      R * mixFamily F N i * R - c • (S * T i * S) := by
    change S * (H⁻¹ * mixFamily F N i - c • (T i * H)) * R = _
    have hn : S * (H⁻¹ * mixFamily F N i) * R = R * mixFamily F N i * R := by
      simp only [← Matrix.mul_assoc, hSJ]
    have ht : S * (T i * H) * R = S * T i * S := by
      simp only [Matrix.mul_assoc, hHR]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hn, ht]
  have hb : firstAction (S * F * S) (whiteThirdSlice R N) =
      fun i => R * mixFamily (S * F) N i * R := by
    rw [firstAction_eq_mixFamily, whiteThirdSlice_eq_mix, mixFamily_mul]
    have hBR : (S * F * S) * R = S * F := by simp only [Matrix.mul_assoc, hSR, Matrix.mul_one]
    rw [hBR]
    exact mixFamily_congruence (S * F) R R N
  change mixFamily S (fun i => whitenedJacobian H (H⁻¹ * mixFamily F N i - c • (T i * H))) = _
  simp_rw [hw]
  rw [mixFamily_sub_smul, mixFamily_congruence S R R (mixFamily F N), mixFamily_mul,
    mixFamily_congruence S S S T]
  rw [hb]
  rfl


def rowLossFinite (H P U : Matrix (Fin n) (Fin n) ℝ)
    (N D T : Fin n → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (H*(U*P*U.transpose)).trace+
    (H*compatibleTraceGram (fun i => completionLeft H H⁻¹ (mixFamily U N i) (D i) (T i))).trace+
      (H*compatibleTraceGram D).trace

def whiteProjectedAction (H U : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) : Fin n → Fin n → Fin n → ℝ :=
  cyclicAverage (firstAction ((inverseSqrtMatrix H)⁻¹*U*(inverseSqrtMatrix H)⁻¹)
    (whiteThirdSlice (inverseSqrtMatrix H) N))

theorem row_loss_projected_control (H P U : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (hP : P.PosSemidef)
    (N D T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ i, (N i).IsSymm) (hT : ∀ i, (T i).IsSymm)
    (hTcyc : ∀ i j k, T i j k=T j k i)
    (hD : ∀ i, (H*D i).IsSymm) :
    cubicEnergy (fun i j k => whiteProjectedAction H U N i j k-
      whiteThirdSlice (inverseSqrtMatrix H)⁻¹ T i j k)/2 ≤ rowLossFinite H P U N D T := by
  let Rq := fun i => completionLeft H H⁻¹ (mixFamily U N i) (D i) (T i)
  have hHJ : H*H⁻¹=1 := Matrix.mul_nonsing_inv H ((Matrix.isUnit_iff_isUnit_det _).mp hH.isUnit)
  have hRq (i : Fin n) : (H*Rq i).IsSymm :=
    (completion_H_compatible H H⁻¹ (mixFamily U N i) (D i) (T i) hHJ
      hH.isHermitian.isSymm (mixFamily_symmetric U N hN i) (hT i) (hD i)).1
  have hdiff : (fun i => Rq i-D i)=fun i => H⁻¹*mixFamily U N i-T i*H := by
    funext i
    dsimp only [Rq,completionLeft]
    abel
  have hWhite := metricWhiteFamily_error H U hH N T 1
  simp only [one_smul,one_mul] at hWhite
  have hEnergy := metricWhiteFamily_energy H hH (fun i => Rq i-D i)
    (fun i => by simpa only [Matrix.mul_sub] using (hRq i).sub (hD i))
  rw [hdiff,hWhite] at hEnergy
  have hHalf := weighted_compatible_half_difference_lower H hH Rq D hRq hD
  rw [hdiff] at hHalf
  have hUP : (U*P*U.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_transpose] using
      hP.conjTranspose_mul_mul_same U.transpose
  have hTarget := trace_mul_nonneg_of_posSemidef hH.posSemidef hUP
  have hCyc := cyclicAverage_energy_le (fun i j k =>
    firstAction ((inverseSqrtMatrix H)⁻¹*U*(inverseSqrtMatrix H)⁻¹)
      (whiteThirdSlice (inverseSqrtMatrix H) N) i j k-
      whiteThirdSlice (inverseSqrtMatrix H)⁻¹ T i j k)
  have hS : ((inverseSqrtMatrix H)⁻¹).IsSymm := (inverseSqrtMatrix_isSymm H).inv
  have hTc (i j k : Fin n) : whiteThirdSlice (inverseSqrtMatrix H)⁻¹ T i j k=
      whiteThirdSlice (inverseSqrtMatrix H)⁻¹ T j k i := whiteThirdSlice_cyclic _ hS T hTcyc i j k
  have hProjection : cyclicAverage (fun i j k =>
      firstAction ((inverseSqrtMatrix H)⁻¹*U*(inverseSqrtMatrix H)⁻¹)
        (whiteThirdSlice (inverseSqrtMatrix H) N) i j k-
        whiteThirdSlice (inverseSqrtMatrix H)⁻¹ T i j k)=
      fun i j k => whiteProjectedAction H U N i j k-whiteThirdSlice (inverseSqrtMatrix H)⁻¹ T i j k := by
    funext i j k
    simp only [cyclicAverage,whiteProjectedAction]
    rw [←hTc i j k,hTc k i j]
    ring
  rw [hProjection] at hCyc
  dsimp only [rowLossFinite]
  dsimp only [Rq] at hHalf
  linarith only [hCyc,hEnergy,hHalf,hTarget]

end KLSConstantImprovement.CoupledCenterMetric
#print axioms KLSConstantImprovement.CoupledCenterMetric.metricWhiteFamily_error
#print axioms KLSConstantImprovement.CoupledCenterMetric.row_loss_projected_control

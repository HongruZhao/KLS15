import KLSConstantImprovement.JointProductionHalfsum
import KLSConstantImprovement.CoupledCenterCoercivity
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder
namespace KLSConstantImprovement.JointProductionStrongCoercivity
open KLS JointProductionHalfsum CoupledCenterMetric CoupledCenterCoercivity
open ActualWeightedWhiteFamily405 ActualResponseProductionHalfSquare405 ActualResponseProductionAlgebra405
open ActualFullSymmetricProduction ActualTensorRowWhite405 ActualFullSymmetricTensorOrdering
open ActualQuarticThirdWhitening405 ActualQuarticWhiteFrame405 ActualQuarticCongruence405
open ActualDirectCubicWhitening405 ActualDirectCubicMomentBinding405 ActualSourceQuarticBinding405
open ActualWhitenedJacobianEnergy405 ActualWhitenedJacobianSymmetry405 ActualResponseCompletionWhitening405
open MixedCubicRankSlicing FourthCubicProjectionDefect
variable {n : ℕ}
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

theorem response_fullSym_production_lower_center_sum (H P F : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef)
    (N D T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN12 : ∀ i j k, N i j k = N j i k) (hN23 : ∀ i j k, N i j k = N i k j)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j)
    (hD : ∀ i, (H * D i).IsSymm) :
    (H * (F * P * F.transpose)).trace +
      4 * (H * matrixTraceGram H T).trace / 3 -
        ((F * H * F.transpose) * matrixTraceGram H⁻¹ N).trace +
          3 * cubicEnergy (hook (firstAction ((inverseSqrtMatrix H)⁻¹ * F * (inverseSqrtMatrix H)⁻¹).transpose
            (whiteThirdSlice (inverseSqrtMatrix H) N))) / 2 +
            (3/2:ℝ) * cubicEnergy (fun i j k =>
              cyclicAverage (firstAction ((inverseSqrtMatrix H)⁻¹*F*(inverseSqrtMatrix H)⁻¹)
                (whiteThirdSlice (inverseSqrtMatrix H) N)) i j k-
                  (2/3:ℝ)*whiteThirdSlice (inverseSqrtMatrix H)⁻¹ T i j k) +
                    (H*compatibleTraceGram (responseSumFamily H F N D T)).trace/2 ≤
              (H * responseProductionMatrix H H⁻¹ P F (mixFamily F N) D T).trace := by
  let R := inverseSqrtMatrix H
  let S := R⁻¹
  have hR : R.IsSymm := inverseSqrtMatrix_isSymm H
  have hS : S.IsSymm := hR.inv
  have hunit : IsUnit R.det := isUnit_iff_ne_zero.mpr (inverseSqrtMatrix_det_ne_zero_of_posDef hH)
  have hRS : R * S = 1 := Matrix.mul_nonsing_inv R hunit
  have hSR : S * R = 1 := Matrix.nonsing_inv_mul R hunit
  have hSS : S * S = H := by
    have he : S.transpose * S = H := inverseSqrtMatrix_inverse_gram hH
    simpa only [hS.eq] using he
  have hRR : R * R = H⁻¹ := by
    unfold R inverseSqrtMatrix
    rw [← Matrix.mul_inv_rev, CFC.sqrt_mul_sqrt_self H hH.posSemidef.nonneg]
  have hNs (i : Fin n) : (N i).IsSymm := Matrix.IsSymm.ext fun j k => hN23 i k j
  have hTs (i : Fin n) : (T i).IsSymm := Matrix.IsSymm.ext fun j k => hT23 i k j
  have hNc (i j k : Fin n) : N i j k = N j k i := (hN12 i j k).trans (hN23 j i k)
  have hTc (i j k : Fin n) : T i j k = T j k i := (hT12 i j k).trans (hT23 j i k)
  let A : Fin n → Matrix (Fin n) (Fin n) ℝ := fun i => H⁻¹ * mixFamily F N i - (2 : ℝ) • (T i * H)
  have hHJ : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H ((Matrix.isUnit_iff_isUnit_det _).mp hH.isUnit)
  have hA (i : Fin n) : (H * A i).IsSymm := by
    have hNF := mixFamily_symmetric F N hNs i
    have hTHT : (H * T i * H).IsSymm := by
      change (H * T i * H).transpose = _
      simp only [Matrix.transpose_mul, hH.isHermitian.isSymm.eq, (hTs i).eq, Matrix.mul_assoc]
    change (H * (H⁻¹ * mixFamily F N i - (2 : ℝ) • (T i * H))).IsSymm
    rw [Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, hHJ, Matrix.one_mul]
    change (mixFamily F N i - (2 : ℝ) • (H * (T i * H))).IsSymm
    change (mixFamily F N i - (2 : ℝ) • (H * (T i * H))).transpose = _
    simp only [Matrix.transpose_sub, Matrix.transpose_smul, hNF.eq,
      Matrix.transpose_mul, hH.isHermitian.isSymm.eq, (hTs i).eq, Matrix.mul_assoc]
  have hE := metricWhiteFamily_energy H hH A hA
  rw [metricWhiteFamily_response_error H F hH N T] at hE
  have hW : cubicEnergy (whiteThirdSlice S T) = (H * matrixTraceGram H T).trace := by
    rw [cubicEnergy_eq_trace_whiteGram _ (whiteThirdSlice_symmetric S hS T hTs),
      whiteGram_whiteThirdSlice S hS T, Matrix.trace_mul_cycle, hSS, rawGram_eq_matrixTraceGram]
  have hRow := white_row_tensor_energy S R F hS hR hSR hRS N hNs
  rw [hSS, hRR, rawGram_eq_matrixTraceGram] at hRow
  have hCoercive := actual_tensor_error_decomposition (S * F * S) (whiteThirdSlice R N) (whiteThirdSlice S T)
    (whiteThirdSlice_cyclic R hR N hNc) (whiteThirdSlice_cyclic S hS T hTc)
  change cubicEnergy (fun i j k => firstAction (S * F * S) (whiteThirdSlice R N) i j k -
    2 * whiteThirdSlice S T i j k) = (H * compatibleTraceGram A).trace at hE
  rw [hW, hRow, hE] at hCoercive
  have hHalf := response_production_exact_squares H P F N D T
  linarith only [hHalf, hCoercive]



theorem response_coarse_center_sum (H P F : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (hP : P.PosSemidef)
    (N D T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN12 : ∀ i j k, N i j k=N j i k) (hN23 : ∀ i j k, N i j k=N i k j)
    (hT12 : ∀ i j k, T i j k=T j i k) (hT23 : ∀ i j k, T i j k=T i k j)
    (hD : ∀ i, (H*D i).IsSymm) :
    4*(H*matrixTraceGram H T).trace/3+
      (3/2:ℝ)*cubicEnergy (fun i j k => whiteProjectedAction H F N i j k-
        (2/3:ℝ)*whiteThirdSlice (inverseSqrtMatrix H)⁻¹ T i j k)+
          cubicEnergy (whiteProjectedCompatible H (responseSumFamily H F N D T))/2 ≤
      (H*responseProductionMatrix H H⁻¹ P F (mixFamily F N) D T).trace+
        ((F*H*F.transpose)*(P+matrixTraceGram H⁻¹ N)).trace := by
  have he := response_fullSym_production_lower_center_sum H P F hH N D T hN12 hN23 hT12 hT23 hD
  have hh := cubicEnergy_nonneg (hook (firstAction ((inverseSqrtMatrix H)⁻¹*F*(inverseSqrtMatrix H)⁻¹).transpose
    (whiteThirdSlice (inverseSqrtMatrix H) N)))
  have hFP : (F*P*F.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_transpose] using
      hP.conjTranspose_mul_mul_same F.transpose
  have hpcol := trace_mul_nonneg_of_posSemidef hH.posSemidef hFP
  have hFH : (F*H*F.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_transpose] using
      hH.posSemidef.conjTranspose_mul_mul_same F.transpose
  have hprow := trace_mul_nonneg_of_posSemidef hFH hP
  have hHJ : H*H⁻¹=1 := Matrix.mul_nonsing_inv H ((Matrix.isUnit_iff_isUnit_det _).mp hH.isUnit)
  have hT (i : Fin n) : (T i).IsSymm := Matrix.IsSymm.ext fun a b => hT23 i b a
  have hN (i : Fin n) : (N i).IsSymm := Matrix.IsSymm.ext fun a b => hN23 i b a
  have hc (i : Fin n) := completion_H_compatible H H⁻¹ (mixFamily F N i) (D i) (T i)
    hHJ hH.isHermitian.isSymm (mixFamily_symmetric F N hN i) (hT i) (hD i)
  have hEnergy := metricWhiteFamily_energy H hH (responseSumFamily H F N D T)
    (fun i => by simpa only [responseSumFamily,Matrix.mul_add] using (hc i).1.add (hc i).2)
  have hProj := cyclicAverage_energy_le (metricWhiteFamily H (responseSumFamily H F N D T))
  change cubicEnergy (whiteProjectedCompatible H (responseSumFamily H F N D T)) ≤ _ at hProj
  dsimp only [whiteProjectedAction]
  rw [Matrix.mul_add,Matrix.trace_add]
  linarith only [he,hh,hpcol,hprow,hEnergy,hProj]

theorem metricWhiteFamily_linear_sub (H : Matrix (Fin n) (Fin n) ℝ)
    (A B : Fin n → Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    metricWhiteFamily H (fun i => c • A i-B i)=
      fun i j k => c*metricWhiteFamily H A i j k-metricWhiteFamily H B i j k := by
  funext i j k
  simp only [metricWhiteFamily,whitenedJacobian,mixFamily,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.mul_smul,Matrix.smul_mul,smul_sub,smul_smul,Matrix.sum_apply,Matrix.sub_apply,
    Matrix.smul_apply,smul_eq_mul,sub_mul,mul_assoc,Finset.sum_sub_distrib,←Finset.mul_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem response_sum_projected_split (H U Z : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef)
    (N D T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    whiteProjectedCompatible H (responseSumFamily H ((2:ℝ) • U-Z) N
      (fun i => (2:ℝ) • D i-T i*H) T)=
      fun i j k => 2*whiteProjectedCompatible H (rowSumFamily H U N D T) i j k-
        whiteProjectedAction H Z N i j k := by
  have hMix (i : Fin n) : mixFamily ((2:ℝ) • U-Z) N i=
      (2:ℝ) • mixFamily U N i-mixFamily Z N i := by
    simp only [mixFamily,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,sub_smul,mul_smul,
      Finset.sum_sub_distrib,←Finset.smul_sum]
  have hFamily : responseSumFamily H ((2:ℝ) • U-Z) N (fun i => (2:ℝ) • D i-T i*H) T=
      fun i => (2:ℝ) • rowSumFamily H U N D T i-H⁻¹*mixFamily Z N i := by
    funext i
    dsimp only [responseSumFamily,rowSumFamily,completionLeft,completionRight]
    rw [hMix]
    simp only [Matrix.mul_sub,Matrix.mul_smul]
    module
  have hAffine := metricWhiteFamily_error H Z hH N T 0
  simp only [zero_smul,sub_zero,zero_mul] at hAffine
  rw [hFamily]
  dsimp only [whiteProjectedCompatible]
  rw [metricWhiteFamily_linear_sub,hAffine]
  funext i j k
  simp only [cyclicAverage,whiteProjectedAction]
  ring

theorem joint_production_eighteen_thirteenths (H P U Z : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (hP : P.PosSemidef)
    (N D T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN12 : ∀ i j k, N i j k=N j i k) (hN23 : ∀ i j k, N i j k=N i k j)
    (hT12 : ∀ i j k, T i j k=T j i k) (hT23 : ∀ i j k, T i j k=T i k j)
    (hD : ∀ i, (H*D i).IsSymm) :
    (18/13:ℝ)*(H*matrixTraceGram H T).trace ≤
      (H*responseProductionMatrix H H⁻¹ P ((2:ℝ) • U-Z) (mixFamily ((2:ℝ) • U-Z) N)
        (fun i => (2:ℝ) • D i-T i*H) T).trace+
      ((((2:ℝ) • U-Z)*H*((2:ℝ) • U-Z).transpose)*(P+matrixTraceGram H⁻¹ N)).trace+
        rowLossFinite H P U N D T/2 := by
  let S := (inverseSqrtMatrix H)⁻¹
  let Tw := whiteThirdSlice S T
  let A := fun i j k => whiteProjectedAction H U N i j k-Tw i j k
  let B := whiteProjectedCompatible H (rowSumFamily H U N D T)
  let Zw := whiteProjectedAction H Z N
  have hNs (i : Fin n) : (N i).IsSymm := Matrix.IsSymm.ext fun a b => hN23 i b a
  have hTs (i : Fin n) : (T i).IsSymm := Matrix.IsSymm.ext fun a b => hT23 i b a
  have hTc (i j k : Fin n) : T i j k=T j k i := (hT12 i j k).trans (hT23 j i k)
  have hDF (i : Fin n) : (H*((2:ℝ) • D i-T i*H)).IsSymm := by
    have hTH : (H*T i*H).IsSymm := by
      change (H*T i*H).transpose=H*T i*H
      simp only [Matrix.transpose_mul,hH.isHermitian.isSymm.eq,(hTs i).eq,Matrix.mul_assoc]
    rw [Matrix.mul_sub,Matrix.mul_smul,←Matrix.mul_assoc]
    change ((2:ℝ) • (H*D i)-H*T i*H).transpose=(2:ℝ) • (H*D i)-H*T i*H
    simp only [Matrix.transpose_sub,Matrix.transpose_smul,(hD i).eq,hTH.eq]
  have hProd := response_coarse_center_sum H P ((2:ℝ) • U-Z) hH hP N
    (fun i => (2:ℝ) • D i-T i*H) T hN12 hN23 hT12 hT23 hDF
  have hRows := row_loss_both_projections H P U hH hP N D T hNs hTs hTc hD
  change cubicEnergy A+cubicEnergy B ≤ 2*rowLossFinite H P U N D T at hRows
  have hCenter : (fun i j k => whiteProjectedAction H ((2:ℝ) • U-Z) N i j k-
      (2/3:ℝ)*whiteThirdSlice (inverseSqrtMatrix H)⁻¹ T i j k)=
      fun i j k => 2*A i j k+(4/3:ℝ)*Tw i j k-Zw i j k := by
    funext i j k
    rw [projected_action_split]
    dsimp only [A,Tw,S,Zw]
    ring
  rw [hCenter,response_sum_projected_split H U Z hH N D T] at hProd
  have hSOS := joint_center_halfsum_square Tw A B Zw
  have hS : S.IsSymm := (inverseSqrtMatrix_isSymm H).inv
  have hSS : S*S=H := by
    have he : S.transpose*S=H := inverseSqrtMatrix_inverse_gram hH
    simpa only [hS.eq] using he
  have hW := direct_white_tensor_square S hS T hTs
  rw [hSS,rawGram_eq_matrixTraceGram] at hW
  change cubicEnergy Tw=(H*matrixTraceGram H T).trace at hW
  linarith only [hProd,hRows,hSOS,hW]

end KLSConstantImprovement.JointProductionStrongCoercivity
#print axioms KLSConstantImprovement.JointProductionStrongCoercivity.response_fullSym_production_lower_center_sum
#print axioms KLSConstantImprovement.JointProductionStrongCoercivity.response_coarse_center_sum
#print axioms KLSConstantImprovement.JointProductionStrongCoercivity.metricWhiteFamily_linear_sub
#print axioms KLSConstantImprovement.JointProductionStrongCoercivity.response_sum_projected_split
#print axioms KLSConstantImprovement.JointProductionStrongCoercivity.joint_production_eighteen_thirteenths

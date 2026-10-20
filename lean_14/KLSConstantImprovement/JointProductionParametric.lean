import KLSConstantImprovement.JointProductionStrongCoercivity
import KLSConstantImprovement.JointProductionParameterSOS
import KLSConstantImprovement.CoupledCenterCoercivity
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder
namespace KLSConstantImprovement.JointProductionParametric
open KLS JointProductionStrongCoercivity JointProductionParameterSOS JointProductionHalfsum CoupledCenterMetric CoupledCenterCoercivity
open ActualWeightedWhiteFamily405 ActualResponseProductionHalfSquare405 ActualResponseProductionAlgebra405
open ActualFullSymmetricProduction ActualTensorRowWhite405 ActualFullSymmetricTensorOrdering
open ActualQuarticThirdWhitening405 ActualQuarticWhiteFrame405 ActualQuarticCongruence405
open ActualDirectCubicWhitening405 ActualDirectCubicMomentBinding405 ActualSourceQuarticBinding405
open ActualWhitenedJacobianEnergy405 ActualWhitenedJacobianSymmetry405 ActualResponseCompletionWhitening405
open MixedCubicRankSlicing FourthCubicProjectionDefect
variable {n : ℕ}
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

theorem joint_production_parameter (H P U Z : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (hP : P.PosSemidef)
    (N D T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN12 : ∀ i j k, N i j k=N j i k) (hN23 : ∀ i j k, N i j k=N i k j)
    (hT12 : ∀ i j k, T i j k=T j i k) (hT23 : ∀ i j k, T i j k=T i k j)
    (hD : ∀ i, (H*D i).IsSymm) {k : ℝ} (hk : 0 ≤ k) :
    (2*(k+4)/(k+6))*(H*matrixTraceGram H T).trace ≤
      (H*responseProductionMatrix H H⁻¹ P ((2:ℝ) • U-Z) (mixFamily ((2:ℝ) • U-Z) N)
        (fun i => (2:ℝ) • D i-T i*H) T).trace+
      ((((2:ℝ) • U-Z)*H*((2:ℝ) • U-Z).transpose)*(P+matrixTraceGram H⁻¹ N)).trace+
        k*rowLossFinite H P U N D T := by
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
  have hSOS := tensor_joint_parameter hk Tw A B Zw
  have hRowsk := mul_le_mul_of_nonneg_left hRows (div_nonneg hk (by norm_num : (0:ℝ) ≤ 2))
  have hS : S.IsSymm := (inverseSqrtMatrix_isSymm H).inv
  have hSS : S*S=H := by
    have he : S.transpose*S=H := inverseSqrtMatrix_inverse_gram hH
    simpa only [hS.eq] using he
  have hW := direct_white_tensor_square S hS T hTs
  rw [hSS,rawGram_eq_matrixTraceGram] at hW
  change cubicEnergy Tw=(H*matrixTraceGram H T).trace at hW
  rw [hW] at hSOS
  have h6 : 0 < k+6 := by linarith
  have hCoef : 2*(k+4)/(k+6)=(4/3:ℝ)+2*k/(3*(k+6)) := by
    field_simp [ne_of_gt h6]
    <;> ring
  rw [hCoef]
  nlinarith only [hProd,hRowsk,hSOS]

end KLSConstantImprovement.JointProductionParametric
#print axioms KLSConstantImprovement.JointProductionParametric.joint_production_parameter

import KLSConstantImprovement.CoupledCenterMetric
import KLSConstantImprovement.CoupledResponseCenter

/-! Stronger coupling: retain the response completion half-sum as well
as its full-symmetric cyclic-center square. The actual response Jacobian
must be2Dq−TH; this crucial same-source relation remains explicit. -/
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder
namespace KLSConstantImprovement.JointProductionHalfsum
open KLS CoupledCenterMetric CoupledCenterFinite CoupledResponseCenter
open ActualWeightedWhiteFamily405 ActualResponseProductionAlgebra405 ActualResponseProductionHalfSquare405
open ActualWhitenedJacobianEnergy405 ActualWhitenedJacobianSymmetry405 ActualResponseCompletionWhitening405
open ActualFullSymmetricProduction ActualFullSymmetricTensorOrdering
open ActualQuarticThirdWhitening405 ActualQuarticWhiteFrame405 ActualQuarticCongruence405
open ActualTensorRowWhite405 ActualDirectCubicWhitening405 ActualSourceQuarticBinding405
open MixedCubicRankSlicing FourthCubicProjectionDefect ActualTensorRowWhite405
variable {ι : Type*} [Fintype ι]
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

theorem joint_center_halfsum_square (T A B Z : ι → ι → ι → ℝ) :
    (2/39:ℝ)*cubicEnergy T ≤ (cubicEnergy A+cubicEnergy B)/4+
      (3/2:ℝ)*cubicEnergy (fun i j k => 2*A i j k+(4/3:ℝ)*T i j k-Z i j k)+
        cubicEnergy (fun i j k => 2*B i j k-Z i j k)/2 := by
  have hp (i j k : ι) : (2/39:ℝ)*(T i j k)^2 ≤ ((A i j k)^2+(B i j k)^2)/4+
      (3/2:ℝ)*(2*A i j k+(4/3:ℝ)*T i j k-Z i j k)^2+(2*B i j k-Z i j k)^2/2 := by
    have hs1 := sq_nonneg ((5/2:ℝ)*A i j k-(6/5:ℝ)*Z i j k+(8/5:ℝ)*T i j k)
    have hs2 := sq_nonneg ((3/2:ℝ)*B i j k-(2/3:ℝ)*Z i j k)
    have hs3 := sq_nonneg (Z i j k-(9/13:ℝ)*T i j k)
    nlinarith only [hs1,hs2,hs3]
  have hh := Finset.sum_le_sum (s:=Finset.univ) fun (i : ι) _ =>
    Finset.sum_le_sum (s:=Finset.univ) fun (j : ι) _ =>
      Finset.sum_le_sum (s:=Finset.univ) fun (k : ι) _ => hp i j k
  simpa only [cubicEnergy,←Finset.mul_sum,Finset.sum_add_distrib,←Finset.sum_div] using hh

variable {n : ℕ}

def responseSumFamily (H F : Matrix (Fin n) (Fin n) ℝ)
    (N D T : Fin n → Matrix (Fin n) (Fin n) ℝ) : Fin n → Matrix (Fin n) (Fin n) ℝ :=
  fun i => completionLeft H H⁻¹ (mixFamily F N i) (D i) (T i)+completionRight H (D i) (T i)

def whiteProjectedCompatible (H : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) : Fin n → Fin n → Fin n → ℝ :=
  cyclicAverage (metricWhiteFamily H A)

def rowSumFamily (H U : Matrix (Fin n) (Fin n) ℝ)
    (N D T : Fin n → Matrix (Fin n) (Fin n) ℝ) : Fin n → Matrix (Fin n) (Fin n) ℝ :=
  fun i => completionLeft H H⁻¹ (mixFamily U N i) (D i) (T i)+D i

theorem response_production_exact_squares (H P F : Matrix (Fin n) (Fin n) ℝ)
    (N D T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (H*responseProductionMatrix H H⁻¹ P F (mixFamily F N) D T).trace=
      (H*(F*P*F.transpose)).trace+
        (H*compatibleTraceGram (fun i => H⁻¹*mixFamily F N i-(2:ℝ) • (T i*H))).trace/2+
          (H*compatibleTraceGram (responseSumFamily H F N D T)).trace/2 := by
  let L := fun i => completionLeft H H⁻¹ (mixFamily F N i) (D i) (T i)
  let R := fun i => completionRight H (D i) (T i)
  have hp := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => (H*M).trace)
    (compatibleTraceGram_parallelogram L R)
  have hd : (fun i => L i-R i)=fun i => H⁻¹*mixFamily F N i-(2:ℝ) • (T i*H) := by
    funext i
    dsimp only [L,R,completionLeft,completionRight]
    module
  rw [hd] at hp
  simp only [Matrix.mul_add,Matrix.mul_smul,Matrix.trace_add,Matrix.trace_smul,smul_eq_mul] at hp
  dsimp only [responseProductionMatrix,responseSumFamily]
  simp only [Matrix.mul_add,Matrix.trace_add]
  dsimp only [L,R] at hp
  change (H*compatibleTraceGram (responseSumFamily H F N D T)).trace+
    (H*compatibleTraceGram (fun i => H⁻¹*mixFamily F N i-(2:ℝ) • (T i*H))).trace=
      2*(H*compatibleTraceGram (fun i => completionLeft H H⁻¹ (mixFamily F N i) (D i) (T i))).trace+
        2*(H*compatibleTraceGram (fun i => completionRight H (D i) (T i))).trace at hp
  linarith only [hp]

theorem row_loss_both_projections (H P U : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (hP : P.PosSemidef)
    (N D T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ i, (N i).IsSymm) (hT : ∀ i, (T i).IsSymm)
    (hTcyc : ∀ i j k, T i j k=T j k i) (hD : ∀ i, (H*D i).IsSymm) :
    cubicEnergy (fun i j k => whiteProjectedAction H U N i j k-
        whiteThirdSlice (inverseSqrtMatrix H)⁻¹ T i j k)+
      cubicEnergy (whiteProjectedCompatible H (rowSumFamily H U N D T)) ≤
        2*rowLossFinite H P U N D T := by
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
  have hMinus := metricWhiteFamily_energy H hH (fun i => Rq i-D i)
    (fun i => by simpa only [Matrix.mul_sub] using (hRq i).sub (hD i))
  have hPlus := metricWhiteFamily_energy H hH (fun i => Rq i+D i)
    (fun i => by simpa only [Matrix.mul_add] using (hRq i).add (hD i))
  have hProjMinus := cyclicAverage_energy_le (metricWhiteFamily H (fun i => Rq i-D i))
  have hProjPlus := cyclicAverage_energy_le (metricWhiteFamily H (fun i => Rq i+D i))
  rw [hdiff,hWhite] at hMinus hProjMinus
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
  rw [hProjection] at hProjMinus
  have hPar := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => (H*M).trace)
    (compatibleTraceGram_parallelogram Rq D)
  simp only [Matrix.mul_add,Matrix.mul_smul,Matrix.trace_add,Matrix.trace_smul,smul_eq_mul] at hPar
  rw [hdiff] at hPar
  have hUP : (U*P*U.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_transpose] using
      hP.conjTranspose_mul_mul_same U.transpose
  have hTarget := trace_mul_nonneg_of_posSemidef hH.posSemidef hUP
  change _+cubicEnergy (cyclicAverage (metricWhiteFamily H (fun i => Rq i+D i))) ≤ _
  dsimp only [rowLossFinite]
  dsimp only [Rq] at hPar hMinus hPlus
  linarith only [hMinus,hPlus,hProjMinus,hProjPlus,hPar,hTarget]

end KLSConstantImprovement.JointProductionHalfsum
#print axioms KLSConstantImprovement.JointProductionHalfsum.joint_center_halfsum_square
#print axioms KLSConstantImprovement.JointProductionHalfsum.response_production_exact_squares
#print axioms KLSConstantImprovement.JointProductionHalfsum.row_loss_both_projections

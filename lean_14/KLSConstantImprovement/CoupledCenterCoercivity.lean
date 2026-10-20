import KLSConstantImprovement.CoupledResponseCenter
import KLSConstantImprovement.ActualAffineWhitening405
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder
namespace KLSConstantImprovement.CoupledCenterCoercivity
open KLS CoupledResponseCenter CoupledCenterMetric CoupledCenterFinite
open ActualResponseProductionAlgebra405 ActualSourceQuarticBinding405
open ActualAffineSlotAlgebra405 ActualAffineWhitening405 ActualAffineFiniteExpansion405
open ActualQuarticThirdWhitening405 ActualQuarticWhiteFrame405 ActualQuarticCongruence405
open ActualDirectCubicWhitening405 ActualDirectCubicMomentBinding405
open ActualFullSymmetricTensorOrdering MixedCubicRankSlicing FourthCubicProjectionDefect
variable {n : ℕ}
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

theorem affine_projected_energy (H A : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (hA : A.IsSymm) (N : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN12 : ∀ i j k, N i j k=N j i k) (hN23 : ∀ i j k, N i j k=N i k j) :
    3*cubicEnergy (whiteProjectedAction H A N)=
      (A*H*A*rawGram H⁻¹ N).trace+2*affineSignedConnection H⁻¹ A N := by
  let Q : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt H
  let R : Matrix (Fin n) (Fin n) ℝ := inverseSqrtMatrix H
  have hQ : Q.IsSymm := (CFC.sqrt_nonneg H).posSemidef.isHermitian.isSymm
  have hR : R.IsSymm := inverseSqrtMatrix_isSymm H
  have hQsq : Q * Q = H := CFC.sqrt_mul_sqrt_self H hH.posSemidef.nonneg
  have hunit : IsUnit Q := (CFC.isUnit_sqrt_iff H hH.posSemidef.nonneg).mpr hH.isUnit
  have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hQR : Q * R = 1 := Matrix.mul_nonsing_inv Q hdet
  have hRQ : R * Q = 1 := Matrix.nonsing_inv_mul Q hdet
  have hRsq : R * R = H⁻¹ := by
    change (CFC.sqrt H)⁻¹ * (CFC.sqrt H)⁻¹ = H⁻¹
    rw [← Matrix.mul_inv_rev, CFC.sqrt_mul_sqrt_self H hH.posSemidef.nonneg]
  have hRtR : R.transpose * R = H⁻¹ := by rw [hR.eq, hRsq]
  have hNs (a : Fin n) : (N a).IsSymm := Matrix.IsSymm.ext fun i j => hN23 a j i
  have hB : (Q * A * Q).IsSymm := by
    change (Q * A * Q).transpose = Q * A * Q
    simp only [Matrix.transpose_mul, hQ.eq, hA.eq, Matrix.mul_assoc]
  have hNw := whiteThirdSlice_full_symmetry R hR N hN12 hN23
  have he1 := affine_signed_whitening Q R A hQR hRQ N
  have he2 := affine_mass_whitening Q R A hR hQR hRQ N
  rw [hRtR] at he1
  rw [hQsq,hRsq] at he2
  have hp := affine_cyclic_projection_energy (Q*A*Q) hB (whiteThirdSlice R N) hNw.1 hNw.2
  have hCyc (i j k : Fin n) : whiteThirdSlice R N i j k=whiteThirdSlice R N j k i :=
    (hNw.1 i j k).trans (hNw.2 j i k)
  rw [←cyclicAverage_first_second (Q*A*Q) (whiteThirdSlice R N) hCyc,he1,he2] at hp
  have hQRinv : Q=(inverseSqrtMatrix H)⁻¹ := by
    change Q=R⁻¹
    have hRRinv : R*R⁻¹=1 := Matrix.mul_nonsing_inv R
      (isUnit_iff_ne_zero.mpr (inverseSqrtMatrix_det_ne_zero_of_posDef hH))
    calc
      Q=Q*1 := by rw [Matrix.mul_one]
      _=Q*(R*R⁻¹) := by rw [hRRinv]
      _=(Q*R)*R⁻¹ := by rw [Matrix.mul_assoc]
      _=R⁻¹ := by rw [hQR,Matrix.one_mul]
  simpa only [whiteProjectedAction,←hQRinv] using hp

theorem projected_action_split (H U Z : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    whiteProjectedAction H ((2:ℝ) • U-Z) N=
      fun i j k => 2*whiteProjectedAction H U N i j k-whiteProjectedAction H Z N i j k := by
  funext i j k
  simp only [whiteProjectedAction,cyclicAverage,firstAction,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.mul_smul,Matrix.smul_mul,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    sub_mul,mul_assoc,Finset.sum_sub_distrib,←Finset.mul_sum]
  ring

theorem coupled_production_pointwise (H P U Z : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (hP : P.PosSemidef) (hZ : Z.IsSymm)
    (N D DF T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN12 : ∀ i j k, N i j k=N j i k) (hN23 : ∀ i j k, N i j k=N i k j)
    (hT12 : ∀ i j k, T i j k=T j i k) (hT23 : ∀ i j k, T i j k=T i k j)
    (hD : ∀ i, (H*D i).IsSymm) (hDF : ∀ i, (H*DF i).IsSymm) :
    (4/3+56/1125:ℝ)*(H*matrixTraceGram H T).trace-
      (7/400:ℝ)*((Z*H*Z*rawGram H⁻¹ N).trace+2*affineSignedConnection H⁻¹ Z N) ≤
      (H*responseProductionMatrix H H⁻¹ P ((2:ℝ) • U-Z) (mixFamily ((2:ℝ) • U-Z) N) DF T).trace+
        ((((2:ℝ) • U-Z)*H*((2:ℝ) • U-Z).transpose)*(P+matrixTraceGram H⁻¹ N)).trace+
          rowLossFinite H P U N D T/2 := by
  let S := (inverseSqrtMatrix H)⁻¹
  let Tw := whiteThirdSlice S T
  let X := fun i j k => whiteProjectedAction H U N i j k-Tw i j k
  let Y := fun i j k => (4/3:ℝ)*Tw i j k-whiteProjectedAction H Z N i j k
  have hNs (i : Fin n) : (N i).IsSymm := Matrix.IsSymm.ext fun a b => hN23 i b a
  have hTs (i : Fin n) : (T i).IsSymm := Matrix.IsSymm.ext fun a b => hT23 i b a
  have hTc (i j k : Fin n) : T i j k=T j k i := (hT12 i j k).trans (hT23 j i k)
  have hRow := row_loss_projected_control H P U hH hP N D T hNs hTs hTc hD
  change cubicEnergy X/2 ≤ rowLossFinite H P U N D T at hRow
  have hProduction := response_fullSym_coarse_center H P ((2:ℝ) • U-Z) hH hP N DF T
    hN12 hN23 hT12 hT23 hDF
  have hCenterEq : (fun i j k => whiteProjectedAction H ((2:ℝ) • U-Z) N i j k-
      (2/3:ℝ)*whiteThirdSlice (inverseSqrtMatrix H)⁻¹ T i j k)=
      fun i j k => 2*X i j k+Y i j k := by
    funext i j k
    rw [projected_action_split]
    dsimp only [X,Y,Tw,S]
    ring
  rw [hCenterEq] at hProduction
  have hCoupled := coupled_center_square X Y
  have hSeparation := affine_target_separation Tw (whiteProjectedAction H Z N)
  have hAffine := affine_projected_energy H Z hH hZ N hN12 hN23
  have hS : S.IsSymm := (inverseSqrtMatrix_isSymm H).inv
  have hSS : S*S=H := by
    have he : S.transpose*S=H := inverseSqrtMatrix_inverse_gram hH
    simpa only [hS.eq] using he
  have hW := direct_white_tensor_square S hS T hTs
  rw [hSS,rawGram_eq_matrixTraceGram] at hW
  change cubicEnergy Tw=(H*matrixTraceGram H T).trace at hW
  change (112/135:ℝ)*cubicEnergy Tw-(7/8:ℝ)*cubicEnergy (whiteProjectedAction H Z N) ≤ cubicEnergy Y at hSeparation
  linarith only [hProduction,hRow,hCoupled,hSeparation,hAffine,hW]

end KLSConstantImprovement.CoupledCenterCoercivity
#print axioms KLSConstantImprovement.CoupledCenterCoercivity.affine_projected_energy

#print axioms KLSConstantImprovement.CoupledCenterCoercivity.projected_action_split
#print axioms KLSConstantImprovement.CoupledCenterCoercivity.coupled_production_pointwise

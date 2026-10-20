import PairTensorStarCoordinates
import PairProjectionNoise

/-! Exact realization of the unordered-pair covariance-noise form by the
released tensor-slot heat correction. This is an identity on actual
coordinates, before inserting any contraction bounds. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators RealInnerProductSpace
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLS.TensorEnergy
open KLSBelow25.PairTensor KLSBelow25.PairProjection
variable {n r : ℕ}
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem actual_pair_star_cons (μ : Measure (Space n))
    (T : Tensor (ι := Fin n) (r+1)) (hT : Symmetric T)
    (i : Fin n) (a : Fin (r+1)→Fin n) :
    KLSBelow25.PairProjection.star (fun e => toHilbert (kernel (actualThirdCubicArray μ) T e)) 0
      (Fin.cons i a)=
    (tensorSlotSum (thirdCumulantMatrix μ (MomentMap.coordinateVector i)) *ᵥ T) a := by
  rw [star_kernel_cons (actualThirdCubicArray μ) (actualThirdCumulant_swap_first μ) T hT]
  simp only [tensorSlotSum,Matrix.sum_mulVec,Finset.sum_apply,
    ←coordinateSlot_eq_tensorSlot,coordinateSlot,actualThirdCubicArray]

theorem actual_pair_diagonal_slot (μ : Measure (Space n))
    (T : Tensor (ι := Fin n) (r+1)) (hT : Symmetric T)
    (s : Fin (r+1)) :
    square (kernel (actualThirdCubicArray μ) T (incidentPair s))=
      ∑ i : Fin n,(tensorSlot s (thirdCumulantMatrix μ (MomentMap.coordinateVector i)) *ᵥ T) ⬝ᵥ
        (tensorSlot s (thirdCumulantMatrix μ (MomentMap.coordinateVector i)) *ᵥ T) := by
  simp only [square,sum_tensor_cons,actual_pair_kernel_cons μ T hT,
    coordinateSlot_eq_tensorSlot,dotProduct,pow_two]

theorem actual_pair_noise_eq (μ : Measure (Space n))
    (T : Tensor (ι := Fin n) (r+1)) (hT : Symmetric T)
    (W : Tensor (ι := Fin n) (r+2)) {Q : ℝ}
    (hQ : ∀ s : Fin (r+1),square (kernel (actualThirdCubicArray μ) T (incidentPair s))=Q) :
    covarianceNoiseForm (toHilbert W)
      (KLSBelow25.PairProjection.star (fun e => toHilbert (kernel (actualThirdCubicArray μ) T e)) 0)
      ((r+1 : ℕ) : ℝ) Q=
    ∑ i : Fin n,energyNoiseCorrection T
      (thirdCumulantMatrix μ (MomentMap.coordinateVector i))
      (fun a => W (Fin.cons i a)) := by
  let V := KLSBelow25.PairProjection.star (fun e => toHilbert (kernel (actualThirdCubicArray μ) T e)) 0
  have hV : V=toHilbert (fun a => V a) := by ext a;rfl
  have hsum : (∑ i : Fin n,∑ s : Fin (r+1),
      (tensorSlot s (thirdCumulantMatrix μ (MomentMap.coordinateVector i)) *ᵥ T) ⬝ᵥ
        (tensorSlot s (thirdCumulantMatrix μ (MomentMap.coordinateVector i)) *ᵥ T))=
      ((r+1 : ℕ) : ℝ)*Q := by
    rw [Finset.sum_comm]
    simp_rw [←actual_pair_diagonal_slot μ T hT,hQ]
    simp
  unfold covarianceNoiseForm
  change ‖toHilbert W‖^2-2*inner ℝ (toHilbert W) V+(1/2:ℝ)*‖V‖^2+
    (1/2:ℝ)*((r+1 : ℕ) : ℝ)*Q=_
  rw [toHilbert_norm_sq,hV,toHilbert_inner,toHilbert_norm_sq]
  simp only [square,pairing,sum_tensor_cons]
  change (∑ i : Fin n,∑ a,W (Fin.cons i a)^2)-
    2*(∑ i : Fin n,∑ a,W (Fin.cons i a)*V (Fin.cons i a))+
    (1/2:ℝ)*(∑ i : Fin n,∑ a,V (Fin.cons i a)^2)+
    (1/2:ℝ)*((r+1 : ℕ) : ℝ)*Q=_
  simp only [V,actual_pair_star_cons μ T hT]
  unfold energyNoiseCorrection
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum]
  rw [hsum]
  simp only [dotProduct,pow_two]
  ring

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actual_pair_noise_eq

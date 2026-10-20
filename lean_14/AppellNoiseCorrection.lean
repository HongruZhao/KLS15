import AppellTensorTwoSlot
import KLS.FullQuadraticVarianceBound
import KLS.WeightedTaylorPermutation

/-! The improved covariance-noise coefficient in manuscript (3.14),
using the actual admissible-law one-slot eight and two-slot four. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ContDiff
namespace KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n r : ℕ}

theorem thirdCumulant_tensor_single_slot_le_eight
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (s : Fin r) (T : (Fin r → Fin n) → ℝ) :
    (∑ k : Fin n,
      (KLS.TensorEnergy.tensorSlot s (thirdCumulantMatrix μ (MomentMap.coordinateVector k)) *ᵥ T) ⬝ᵥ
      (KLS.TensorEnergy.tensorSlot s (thirdCumulantMatrix μ (MomentMap.coordinateVector k)) *ᵥ T)) ≤
      8*(T ⬝ᵥ T) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  exact KLS.TensorEnergy.tensorSlot_noise_sum_le _
    (fun k => (thirdCumulantMatrix_isSymm _ _).eq) 8
    (hμ.isotropic.thirdCumulantMatrix_seed_eight hμ.quadraticVarianceEight_unconditional) s T

theorem thirdCumulant_tensor_all_single_slots_le_eight_rank
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : (Fin r → Fin n) → ℝ) :
    (∑ k : Fin n, ∑ s : Fin r,
      (KLS.TensorEnergy.tensorSlot s (thirdCumulantMatrix μ (MomentMap.coordinateVector k)) *ᵥ T) ⬝ᵥ
      (KLS.TensorEnergy.tensorSlot s (thirdCumulantMatrix μ (MomentMap.coordinateVector k)) *ᵥ T)) ≤
      8*(r:ℝ)*(T ⬝ᵥ T) := by
  rw [Finset.sum_comm]
  have h := Finset.sum_le_sum (s:=Finset.univ)
    (fun s _ => thirdCumulant_tensor_single_slot_le_eight hμ s T)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm,mul_left_comm,mul_assoc] using h

 theorem square_completion_scalar {β : ℝ} (hβ : β < 1) (w v : ℝ) :
    β*w^2-(1/(1-β)-1/2)*v^2 ≤ w^2-2*w*v+(1/2)*v^2 := by
  have hδ : 0 < 1-β := by linarith
  have hid : (1-β)*((w^2-2*w*v+(1/2)*v^2)-
      (β*w^2-(1/(1-β)-1/2)*v^2)) = ((1-β)*w-v)^2 := by
    field_simp
    <;> ring
  nlinarith [sq_nonneg ((1-β)*w-v)]

 theorem square_completion_dot {ι : Type*} [Fintype ι] {β : ℝ}
    (hβ : β < 1) (W V : ι → ℝ) :
    β*(W ⬝ᵥ W)-(1/(1-β)-1/2)*(V ⬝ᵥ V) ≤
      W ⬝ᵥ W-2*(W ⬝ᵥ V)+(1/2)*(V ⬝ᵥ V) := by
  have h := Finset.sum_le_sum (s:=Finset.univ)
    (fun i _ => square_completion_scalar hβ (W i) (V i))
  simpa only [dotProduct,pow_two,Finset.sum_sub_distrib,Finset.sum_add_distrib,
    ← Finset.mul_sum,mul_assoc] using h

/-- The exact improved noise bound. The covariance drift -r||T||² must
still be added to obtain the full energy drift in manuscript (3.14). -/
theorem sum_energyNoiseCorrection_lower_two_slot
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {T : (Fin r → Fin n) → ℝ} (hT : CoordinateTensorSymmetric T)
    (W : Fin n → (Fin r → Fin n) → ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    β*(∑ k : Fin n, W k ⬝ᵥ W k) -
      ((4/(1-β)-2)*(r:ℝ)^2+((4/(1-β)-2)-4)*(r:ℝ))*(T ⬝ᵥ T) ≤
      ∑ k : Fin n, KLS.TensorEnergy.energyNoiseCorrection T
        (thirdCumulantMatrix μ (MomentMap.coordinateVector k)) (W k) := by
  let H := fun k => thirdCumulantMatrix μ (MomentMap.coordinateVector k)
  let V := fun k => KLS.TensorEnergy.tensorSlotSum (H k) *ᵥ T
  let S := ∑ k : Fin n, ∑ s : Fin r,
    (KLS.TensorEnergy.tensorSlot s (H k) *ᵥ T) ⬝ᵥ
    (KLS.TensorEnergy.tensorSlot s (H k) *ᵥ T)
  let η : ℝ := 1/(1-β)-1/2
  have hη : 1/2 ≤ η := by
    dsimp [η]
    have hδ : 0 < 1-β := by linarith
    have hdiv : 1 ≤ 1/(1-β) := (le_div_iff₀ hδ).mpr (by linarith)
    linarith
  have hv : (∑ k : Fin n, V k ⬝ᵥ V k) ≤ S+4*(r:ℝ)*((r:ℝ)-1)*(T ⬝ᵥ T) :=
    thirdCumulant_tensorSlotSum_square_le hμ hT
  have hs : S ≤ 8*(r:ℝ)*(T ⬝ᵥ T) := thirdCumulant_tensor_all_single_slots_le_eight_rank hμ T
  have hy := Finset.sum_le_sum (s:=Finset.univ)
    (fun k _ => add_le_add_right (square_completion_dot hβ1 (W k) (V k))
      ((1/2:ℝ)*∑ s : Fin r,
        (KLS.TensorEnergy.tensorSlot s (H k) *ᵥ T) ⬝ᵥ
        (KLS.TensorEnergy.tensorSlot s (H k) *ᵥ T)))
  have hy' : (∑ k : Fin n, (β*(W k ⬝ᵥ W k)-η*(V k ⬝ᵥ V k)+
      (1/2:ℝ)*(∑ s : Fin r,
        (KLS.TensorEnergy.tensorSlot s (H k) *ᵥ T) ⬝ᵥ
        (KLS.TensorEnergy.tensorSlot s (H k) *ᵥ T)))) ≤
      ∑ k : Fin n, KLS.TensorEnergy.energyNoiseCorrection T (H k) (W k) := by
    convert hy using 1
    · apply Finset.sum_congr rfl
      intro k _
      dsimp [η]
      ring
    · apply Finset.sum_congr rfl
      intro k _
      dsimp [KLS.TensorEnergy.energyNoiseCorrection,V]
      ring
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum] at hy'
  change β*(∑ k : Fin n, W k ⬝ᵥ W k)-η*(∑ k : Fin n,V k ⬝ᵥ V k)+(1/2:ℝ)*S ≤ _ at hy'
  have hv' := mul_le_mul_of_nonneg_left hv (by linarith : 0 ≤ η)
  have hs' := mul_le_mul_of_nonneg_left hs (by linarith : 0 ≤ η-1/2)
  have heq : ((4/(1-β)-2)*(r:ℝ)^2+((4/(1-β)-2)-4)*(r:ℝ))*(T ⬝ᵥ T) =
      (η-1/2)*(8*(r:ℝ)*(T ⬝ᵥ T))+η*(4*(r:ℝ)*((r:ℝ)-1)*(T ⬝ᵥ T)) := by
    dsimp [η]
    ring
  rw [heq]
  linarith

/-- Actual normalized Taylor coefficients have the required tensor symmetry. -/
theorem exponentialTiltCoordinateTaylor_symmetric
    {φ : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    {f : Space n → ℝ} (hf : MemLp f 2 (potentialMeasure φ)) :
    CoordinateTensorSymmetric (exponentialTiltCoordinateTaylor φ f r) := by
  intro s t a
  exact exponentialTiltCoordinateTaylor_comp_perm hφ hκ hlower hf r a (Equiv.swap s t)

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.thirdCumulant_tensor_all_single_slots_le_eight_rank
#print axioms KLS.DeterministicBridgeIntegration.sum_energyNoiseCorrection_lower_two_slot
#print axioms KLS.DeterministicBridgeIntegration.exponentialTiltCoordinateTaylor_symmetric

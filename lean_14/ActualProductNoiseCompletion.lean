import ActualProductSingleSlot
import AppellNoiseCorrection

/-!
All-rank covariance noise bound for the actual centered exponential product.
The exact single-slot identity is retained, so the positive single-slot term
is not weakened together with the negative slot-sum term. The statement is a
finite tensor inequality and needs no admissibility or integrability premise.
-/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLSImprovement.ActualProductNoiseCompletion
open KLS KLS.TensorEnergy KLS.DeterministicBridgeIntegration
open KLSImprovement.ActualProductSingleSlot
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Exact dot-product completion, before discarding its nonnegative square. -/
theorem square_completion_dot_exact {ι : Type*} [Fintype ι]
    {β : ℝ} (hβ1 : β<1) (W V : ι → ℝ) :
    W ⬝ᵥ W-2*(W ⬝ᵥ V)+(1/2 : ℝ)*(V ⬝ᵥ V) =
      β*(W ⬝ᵥ W)-(1/(1-β)-1/2)*(V ⬝ᵥ V)+
        (1-β)*((fun i => W i-V i/(1-β)) ⬝ᵥ (fun i => W i-V i/(1-β))) := by
  have hδ : 1-β≠0 := ne_of_gt (by linarith : 0<1-β)
  have hp (i : ι) :
      W i*W i-2*(W i*V i)+(1/2 : ℝ)*(V i*V i) =
        β*(W i*W i)-(1/(1-β)-1/2)*(V i*V i)+
          (1-β)*((W i-V i/(1-β))*(W i-V i/(1-β))) := by
    field_simp [hδ]
    ring
  have hs := Finset.sum_congr (s₁:=Finset.univ) (s₂:=Finset.univ) rfl (fun i _ => hp i)
  simpa only [dotProduct, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum] using hs

/-- Exact energy-noise identity valid for every matrix, before applying a law
or a matrix cap. Its final term is the discarded square-completion defect. -/
theorem energy_noise_square_completion_exact {n r : ℕ}
    (T : (Fin r → Fin n) → ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (W : (Fin r → Fin n) → ℝ) {β : ℝ} (hβ1 : β<1) :
    energyNoiseCorrection T H W =
      β*(W ⬝ᵥ W)-
        (1/(1-β)-1/2)*((tensorSlotSum H *ᵥ T) ⬝ᵥ (tensorSlotSum H *ᵥ T))+
      (1/2 : ℝ)*(∑ s : Fin r,
        (tensorSlot s H *ᵥ T) ⬝ᵥ (tensorSlot s H *ᵥ T))+
      (1-β)*((fun a => W a-(tensorSlotSum H *ᵥ T) a/(1-β)) ⬝ᵥ
        (fun a => W a-(tensorSlotSum H *ᵥ T) a/(1-β))) := by
  have hs := square_completion_dot_exact hβ1 W (tensorSlotSum H *ᵥ T)
  unfold energyNoiseCorrection
  linarith

/-- Product-specific all-rank square-completion bound. -/
theorem product_energy_noise_lower {n r : ℕ}
    (T : (Fin r → Fin n) → ℝ)
    (W : Fin n → (Fin r → Fin n) → ℝ)
    {β : ℝ} (hβ0 : 0≤β) (hβ1 : β<1) :
    β*(∑ k : Fin n, W k ⬝ᵥ W k)-
      ((4/(1-β)-2)*(r : ℝ)^2-2*(r : ℝ))*(T ⬝ᵥ T) ≤
      ∑ k : Fin n, energyNoiseCorrection T (productCumulantMatrix n k) (W k) := by
  let V := fun k : Fin n => tensorSlotSum (productCumulantMatrix n k) *ᵥ T
  let S := ∑ k : Fin n, ∑ s : Fin r,
    (tensorSlot s (productCumulantMatrix n k) *ᵥ T) ⬝ᵥ
      (tensorSlot s (productCumulantMatrix n k) *ᵥ T)
  let η : ℝ := 1/(1-β)-1/2
  have hη : 0≤η := by
    have hδ : 0<1-β := by linarith
    have hdiv : 1≤1/(1-β) := (le_div_iff₀ hδ).mpr (by linarith)
    dsimp [η]
    linarith
  have hS : S=4*(r : ℝ)*(T ⬝ᵥ T) := by
    dsimp [S]
    rw [Finset.sum_comm]
    exact product_tensor_all_single_slots_exact T
  have hv : (∑ k : Fin n, V k ⬝ᵥ V k)≤4*(r : ℝ)^2*(T ⬝ᵥ T) :=
    product_tensor_slot_sum_bound T
  have hy := Finset.sum_le_sum (s:=Finset.univ)
    (fun k _ => add_le_add_right (square_completion_dot hβ1 (W k) (V k))
      ((1/2 : ℝ)*∑ s : Fin r,
        (tensorSlot s (productCumulantMatrix n k) *ᵥ T) ⬝ᵥ
          (tensorSlot s (productCumulantMatrix n k) *ᵥ T)))
  have hy' : (∑ k : Fin n, (β*(W k ⬝ᵥ W k)-η*(V k ⬝ᵥ V k)+
      (1/2 : ℝ)*(∑ s : Fin r,
        (tensorSlot s (productCumulantMatrix n k) *ᵥ T) ⬝ᵥ
          (tensorSlot s (productCumulantMatrix n k) *ᵥ T)))) ≤
      ∑ k : Fin n, energyNoiseCorrection T (productCumulantMatrix n k) (W k) := by
    convert hy using 1
    · apply Finset.sum_congr rfl
      intro k _
      dsimp [η]
      ring
    · apply Finset.sum_congr rfl
      intro k _
      dsimp [energyNoiseCorrection,V]
      ring
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hy'
  change β*(∑ k : Fin n, W k ⬝ᵥ W k)-η*(∑ k : Fin n, V k ⬝ᵥ V k)+
    (1/2 : ℝ)*S ≤ _ at hy'
  have hv' := mul_le_mul_of_nonneg_left hv hη
  have he : ((4/(1-β)-2)*(r : ℝ)^2-2*(r : ℝ))*(T ⬝ᵥ T) =
      η*(4*(r : ℝ)^2*(T ⬝ᵥ T))-(1/2 : ℝ)*(4*(r : ℝ)*(T ⬝ᵥ T)) := by
    dsimp [η]
    ring
  rw [he]
  linarith

/-- Adding the covariance drift -r||T||² gives the improved generator loss. -/
theorem product_noise_with_covariance_lower {n r : ℕ}
    (T : (Fin r → Fin n) → ℝ)
    (W : Fin n → (Fin r → Fin n) → ℝ)
    {β : ℝ} (hβ0 : 0≤β) (hβ1 : β<1) :
    β*(∑ k : Fin n, W k ⬝ᵥ W k)-
      ((4/(1-β)-2)*(r : ℝ)^2-(r : ℝ))*(T ⬝ᵥ T) ≤
      (∑ k : Fin n, energyNoiseCorrection T (productCumulantMatrix n k) (W k))-
        (r : ℝ)*(T ⬝ᵥ T) := by
  have hn := product_energy_noise_lower T W hβ0 hβ1
  nlinarith

/-- Exact improvement over the coefficient in the original uniform bound. -/
theorem old_generator_coefficient_sub_product {r : ℕ} {β : ℝ} (hβ1 : β<1) :
    ((4/(1-β)-2)*(r : ℝ)^2+((4/(1-β)-2)-3)*(r : ℝ))-
      ((4/(1-β)-2)*(r : ℝ)^2-(r : ℝ)) = 4*β*(r : ℝ)/(1-β) := by
  have hδ : 1-β≠0 := ne_of_gt (by linarith : 0<1-β)
  field_simp [hδ]
  ring

theorem product_generator_coefficient_le_old {r : ℕ} {β : ℝ}
    (hβ0 : 0≤β) (hβ1 : β<1) :
    (4/(1-β)-2)*(r : ℝ)^2-(r : ℝ) ≤
      (4/(1-β)-2)*(r : ℝ)^2+((4/(1-β)-2)-3)*(r : ℝ) := by
  have hd := old_generator_coefficient_sub_product (r:=r) hβ1
  have hn : 0≤4*β*(r : ℝ)/(1-β) := by positivity
  linarith

end KLSImprovement.ActualProductNoiseCompletion

#print axioms KLSImprovement.ActualProductNoiseCompletion.product_energy_noise_lower
#print axioms KLSImprovement.ActualProductNoiseCompletion.product_noise_with_covariance_lower
#print axioms KLSImprovement.ActualProductNoiseCompletion.old_generator_coefficient_sub_product
#print axioms KLSImprovement.ActualProductNoiseCompletion.product_generator_coefficient_le_old

#print axioms KLSImprovement.ActualProductNoiseCompletion.square_completion_dot_exact
#print axioms KLSImprovement.ActualProductNoiseCompletion.energy_noise_square_completion_exact

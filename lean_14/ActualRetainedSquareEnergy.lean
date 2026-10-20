import ActualAppellEnergyEvolution
import RetainedSquareIdentity

/-! A precise actual-law reduction for the retained-square research route.
The mixed surplus bound is explicit. It is not asserted at joint maximizers. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.TensorEnergy KLS.DeterministicBridgeNext
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

def actualAppellSlotResponse (μ : Measure (Space n)) (f : Space n → ℝ)
    (d : ℕ) (i : Fin n) : (Fin d → Fin n) → ℝ :=
  tensorSlotSum (thirdCumulantMatrix μ (MomentMap.coordinateVector i)) *ᵥ
    actualAppellCoefficient μ f d

def actualAppellMixedSurplus (μ : Measure (Space n)) (f : Space n → ℝ) (d : ℕ) : ℝ :=
  ∑ i : Fin n,
    ((fun a => actualAppellCoefficient μ f (d+1) (Fin.cons i a))-
      actualAppellSlotResponse μ f d i) ⬝ᵥ actualAppellSlotResponse μ f d i

theorem retained_square_dot_identity {ι : Type*} [Fintype ι]
    (W V : ι → ℝ) (α : ℝ) :
    W ⬝ᵥ W-2*(W ⬝ᵥ V)+(1/2 : ℝ)*(V ⬝ᵥ V) =
      α*(W ⬝ᵥ W)-(α+1/2)*(V ⬝ᵥ V)-2*α*((W-V) ⬝ᵥ V)+
        (1-α)*((W-V) ⬝ᵥ (W-V)) := by
  simp only [sub_dotProduct,dotProduct_sub,dotProduct_comm V W]
  ring

theorem actualAppell_noise_lower_of_mixed_surplus
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ)
    {α M : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hmixed : actualAppellMixedSurplus μ f d ≤ M) :
    α*actualAppellEnergy μ f (d+1)-
      ((2+4*α)*(d : ℝ)^2+((2+4*α)-4)*(d : ℝ))*actualAppellEnergy μ f d-
      2*α*M ≤
      ∑ i : Fin n, energyNoiseCorrection (actualAppellCoefficient μ f d)
        (thirdCumulantMatrix μ (MomentMap.coordinateVector i))
        (fun a => actualAppellCoefficient μ f (d+1) (Fin.cons i a)) := by
  let T := actualAppellCoefficient μ f d
  let H := fun i => thirdCumulantMatrix μ (MomentMap.coordinateVector i)
  let V := fun i => tensorSlotSum (H i) *ᵥ T
  let W := fun (i : Fin n) (a : Fin d → Fin n) =>
    actualAppellCoefficient μ f (d+1) (Fin.cons i a)
  let S := ∑ i : Fin n, ∑ s : Fin d,
    (tensorSlot s (H i) *ᵥ T) ⬝ᵥ (tensorSlot s (H i) *ᵥ T)
  let η : ℝ := α+1/2
  have hv : (∑ i : Fin n, V i ⬝ᵥ V i) ≤ S+4*(d : ℝ)*((d : ℝ)-1)*(T ⬝ᵥ T) :=
    actualAppell_tensorSlotSum_square_le hμ hf
  have hs : S ≤ 8*(d : ℝ)*(T ⬝ᵥ T) :=
    thirdCumulant_tensor_all_single_slots_le_eight_rank hμ T
  have hy := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    (show α*(W i ⬝ᵥ W i)-η*(V i ⬝ᵥ V i)-2*α*((W i-V i) ⬝ᵥ V i)+
      (1/2 : ℝ)*(∑ s : Fin d,
        (tensorSlot s (H i) *ᵥ T) ⬝ᵥ (tensorSlot s (H i) *ᵥ T)) ≤
        energyNoiseCorrection T (H i) (W i) from by
      rw [energyNoiseCorrection,retained_square_dot_identity (W i) (V i) α]
      have hp := mul_nonneg (sub_nonneg.mpr hα1)
        (dotProduct_self_nonnegative (W i-V i))
      dsimp [η]
      linarith))
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum] at hy
  change α*(∑ i : Fin n, W i ⬝ᵥ W i)-η*(∑ i : Fin n,V i ⬝ᵥ V i)-
    2*α*(∑ i : Fin n,(W i-V i) ⬝ᵥ V i)+(1/2 : ℝ)*S ≤ _ at hy
  have hm : (∑ i : Fin n,(W i-V i) ⬝ᵥ V i) ≤ M := hmixed
  have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2*α by positivity)
  have hv' := mul_le_mul_of_nonneg_left hv (show 0 ≤ η by dsimp [η]; linarith)
  have hs' := mul_le_mul_of_nonneg_left hs hα0
  have heq : ((2+4*α)*(d : ℝ)^2+((2+4*α)-4)*(d : ℝ))*(T ⬝ᵥ T) =
      α*(8*(d : ℝ)*(T ⬝ᵥ T))+η*(4*(d : ℝ)*((d : ℝ)-1)*(T ⬝ᵥ T)) := by
    dsimp [η]
    ring
  rw [actualAppell_next_slices_square] at hy
  change _ ≤ ∑ i : Fin n,energyNoiseCorrection T (H i) (W i)
  rw [actualAppellEnergy_eq_dotProduct μ f d,
    ← show T = actualAppellCoefficient μ f d from rfl,heq]
  dsimp [η] at hv' hy ⊢
  linarith

/-- The genuine energy generator has the improved leading coefficient
2+4α if the explicitly stated mixed surplus estimate is established. -/
theorem actualAppell_generator_lower_of_mixed_surplus
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ)
    {α M : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hmixed : actualAppellMixedSurplus μ f d ≤ M) :
    α*actualAppellEnergy μ f (d+1)-
      ((2+4*α)*(d : ℝ)^2+((2+4*α)-3)*(d : ℝ))*actualAppellEnergy μ f d-
      2*α*M-2*(actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d) ≤
    localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1)
      (fun s z => actualCovarianceAppellEnergy (actualDampedTiltLaw μ z s) f d) := by
  have hn := actualAppell_noise_lower_of_mixed_surplus hμ hf hα0 hα1 hmixed
  rw [actualCovarianceAppellEnergy_generator_exact hμ hf d]
  nlinarith

/-- An O(d) mixed surplus changes only the linear-in-rank loss, while
the leading covariance coefficient becomes 2+4α. -/
theorem actualAppell_generator_lower_of_linear_surplus
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ)
    {α L : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hmixed : actualAppellMixedSurplus μ f d ≤
      L*(d : ℝ)*actualAppellEnergy μ f d) :
    α*actualAppellEnergy μ f (d+1)-
      ((2+4*α)*(d : ℝ)^2+(4*α-1+2*α*L)*(d : ℝ))*actualAppellEnergy μ f d-
      2*(actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d) ≤
    localHeatGenerator (fun i : Fin n => EuclideanSpace.single i 1)
      (fun s z => actualCovarianceAppellEnergy (actualDampedTiltLaw μ z s) f d) := by
  have h := actualAppell_generator_lower_of_mixed_surplus hμ hf hα0 hα1 hmixed
  convert h using 1 <;> ring

/-- Arithmetic model of the adjacent-degree centered-exponential Appell
pairing: W=2(d+1)T and V=2dT. This is not an encoded exponential law. -/
theorem exponential_adjacent_degree_surplus_model (d t : ℝ) :
    (2*(d+1)*t-2*d*t)*(2*d*t) = 4*d*t^2 := by ring

#print axioms actualAppell_noise_lower_of_mixed_surplus
#print axioms actualAppell_generator_lower_of_mixed_surplus
#print axioms actualAppell_generator_lower_of_linear_surplus
#print axioms exponential_adjacent_degree_surplus_model
end KLS.DeterministicBridgeIntegration

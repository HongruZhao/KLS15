import ActualGeneralResidualNoise
import ActualPairAppellRemainder

/-! Signed completion of the size-two proper row at every rank.
The noise and the row share the same actual cubic creation tensor.
No improved universal tensor constant is assumed. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators RealInnerProductSpace
namespace KLSConstantImprovement.SignedRowNoise
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSBelow25.PairTensor KLSBelow25.PairProjection
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

theorem pair_projection_signed_noise
    {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U : Pair N → H) (W : H) (i : Fin N)
    {Q R S t β E γ : ℝ} (hN : 4 ≤ N) (hGram : Gram U Q R S)
    (hConstant : ∀ e, inner ℝ W (U e) = t)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hγ : 1 ≤ γ)
    (hlo : 2*γ^2 ≤ (N : ℝ)*(1-β))
    (hR : R ≤ 4*E) (hS : S ≤ (4+8/(3*((N : ℝ)-2)))*E) :
    β*‖W‖^2-(γ^2*leadingNoiseCoefficient ((N : ℝ)-1)/(1-β)-
      positiveNoiseCoefficient ((N : ℝ)-1))*E ≤
    covarianceNoiseForm W (star U i) ((N : ℝ)-1) Q-
      2*(γ-1)*inner ℝ W (star U i) := by
  have hγp : 0 < γ := by linarith
  have hγs : 0 < γ^2 := sq_pos_of_pos hγp
  have hγone : 1 ≤ γ^2 := by nlinarith
  have hn : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  let b : ℝ := 1-(1-β)/γ^2
  have hb0 : 0 ≤ b := by
    dsimp [b]
    have hh : (1-β)/γ^2 ≤ 1 := (div_le_one hγs).mpr (by linarith)
    linarith
  have hbhi : b ≤ ((N : ℝ)-2)/(N : ℝ) := by
    apply (le_div_iff₀ hn).mpr
    dsimp [b]
    apply (mul_le_mul_iff_right₀ hγs).mp
    field_simp
    nlinarith
  have hc : ∀ e, inner ℝ (γ • W) (U e) = γ*t := by
    intro e
    rw [real_inner_smul_left,hConstant]
  have hh := pair_projection_noise_low U (γ • W) i hN hGram hc hb0 hbhi hR hS
  have hden : 1-b = (1-β)/γ^2 := by dsimp [b]; ring
  have hcoef : b*γ^2 = γ^2-1+β := by dsimp [b]; field_simp; ring
  have hnorm : ‖γ • W‖^2 = γ^2*‖W‖^2 := by
    rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  have hdiv : leadingNoiseCoefficient ((N : ℝ)-1)/(1-b) =
      γ^2*leadingNoiseCoefficient ((N : ℝ)-1)/(1-β) := by
    rw [hden]
    field_simp
  unfold covarianceNoiseForm at hh ⊢
  rw [hnorm,real_inner_smul_left,hdiv] at hh
  rw [←mul_assoc,hcoef] at hh
  nlinarith

variable {n r : ℕ}

theorem actual_all_rank_signed_pair_noise
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Tensor (ι := Fin n) (r+3)) (hT : Symmetric T)
    (W : Tensor (ι := Fin n) (r+4)) (hW : Symmetric W)
    {β γ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hγ : 1 ≤ γ)
    (hlo : 2*γ^2 ≤ ((r : ℝ)+4)*(1-β)) :
    β*square W-(γ^2*leadingNoiseCoefficient ((r : ℝ)+3)/(1-β)-
      positiveNoiseCoefficient ((r : ℝ)+3))*square T ≤
    (∑ i : Fin n, KLS.TensorEnergy.energyNoiseCorrection T
      (thirdCumulantMatrix μ (MomentMap.coordinateVector i))
      (fun a => W (Fin.cons i a)))-
      (4*(γ-1)/((r : ℝ)+4))*pairing W (creation (actualThirdCubicArray μ) T) := by
  let U := fun e : Pair (r+4) => toHilbert (kernel (actualThirdCubicArray μ) T e)
  let e0 := incidentPair (0 : Fin (r+3))
  let e1 := incidentPair (1 : Fin (r+3))
  let Q := pairing (kernel (actualThirdCubicArray μ) T e0)
    (kernel (actualThirdCubicArray μ) T e0)
  let R := pairing (kernel (actualThirdCubicArray μ) T e0)
    (kernel (actualThirdCubicArray μ) T e1)
  let S := pairing (kernel (actualThirdCubicArray μ) T e0)
    (kernel (actualThirdCubicArray μ) T (disjointPair r))
  have hg : Gram U Q R S := kernel_gram_of_representatives (actualThirdCubicArray μ)
    (actualThirdCumulant_swap_first μ) T hT e0 e1 (disjointPair r)
    (incident_intersection_card _ _ (by norm_num [Fin.ext_iff])) disjoint_intersection_card
  have hc : ∀ e, inner ℝ (toHilbert W) (U e) =
      pairing T (annihilation (actualThirdCubicArray μ) W) := by
    intro e
    rw [real_inner_comm]
    exact (toHilbert_inner _ _).trans (kernel_pairing_annihilation _ T W hW e)
  have hR : R ≤ 4*square T := actual_pair_kernel_cross_le_four hμ T hT 0 1
    (by norm_num [Fin.ext_iff])
  have hS : S ≤ (4+8/(3*(((r+4 : ℕ) : ℝ)-2)))*square T := by
    have hh := actual_pair_disjoint_le hμ T hT
    dsimp only [S,e0]
    convert hh using 1 <;> push_cast <;> ring_nf
  have hlo' : 2*γ^2 ≤ ((r+4 : ℕ) : ℝ)*(1-β) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hlo
  have hh := pair_projection_signed_noise U (toHilbert W) (0 : Fin (r+4))
    (by omega) hg hc hβ0 hβ1 hγ hlo' hR hS
  have hQ : ∀ s : Fin (r+3), square (kernel (actualThirdCubicArray μ) T (incidentPair s)) = Q := by
    intro s
    have hd := hg (incidentPair s) (incidentPair s)
    simpa only [Gram,ite_true,U,toHilbert_inner,pairing,square,pow_two] using hd
  have he := actual_pair_noise_eq μ T hT W hQ
  have hi := constant_pairing U (toHilbert W) hc (0 : Fin (r+4))
  unfold projection at hi
  rw [real_inner_smul_right] at hi
  have hsum : sumPairs U = toHilbert (creation (actualThirdCubicArray μ) T) :=
    pair_sum_toHilbert (actualThirdCubicArray μ) T
  rw [hsum,toHilbert_inner] at hi
  have hn : ((r+3 : ℕ) : ℝ) = ((r+4 : ℕ) : ℝ)-1 := by push_cast; ring
  rw [hn] at he
  rw [he,hi,toHilbert_norm_sq] at hh
  convert hh using 1 <;> push_cast <;> ring

end KLSConstantImprovement.SignedRowNoise
#print axioms KLSConstantImprovement.SignedRowNoise.pair_projection_signed_noise
#print axioms KLSConstantImprovement.SignedRowNoise.actual_all_rank_signed_pair_noise

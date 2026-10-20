import KLSConstantImprovement.SignedRowNoise

/-! Complementary branch and unrestricted signed pair-noise control. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators RealInnerProductSpace
namespace KLSConstantImprovement.SignedRowNoiseHigh
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSBelow25.PairTensor KLSBelow25.PairProjection
open KLSConstantImprovement.SignedRowNoise
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

def highLeading (d : ℝ) : ℝ := 4*d^2+8*d/3
def highPositive (d : ℝ) : ℝ := 2*d^2+6*d

theorem high_noise_bound_of_projection_data
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (W V P : H) {d Q R S δ E : ℝ}
    (hd : 3≤d) (hδ : 0<δ) (hδhi : (d+1)*δ≤2)
    (hinner : inner ℝ W V=inner ℝ W P)
    (hV : ‖V‖^2=d*Q+d*(d-1)*R)
    (hP : ‖P‖^2=(2*d/(d+1))*(Q+2*(d-1)*R+((d-1)*(d-2)/2)*S))
    (hQ : Q≤8*E) (hR : R≤4*E) (hS : S≤(4+8/(3*(d-1)))*E) :
    (1-δ)*‖W‖^2-(highLeading d/δ-highPositive d)*E≤
      covarianceNoiseForm W V d Q := by
  have hc := pair_noise_completion_of_projection_data W V P hd hδ hinner hV hP
  have hd0 : 0<d := by linarith
  have hdm : 0<d-1 := by linarith
  have hden : 0<(d+1)*δ := mul_pos (by linarith) hδ
  have hqc : d-2*d/((d+1)*δ)≤0 := by
    apply sub_nonpos.mpr
    apply (le_div_iff₀ hden).mpr
    nlinarith [mul_le_mul_of_nonneg_left hδhi hd0.le]
  have hbase : (1:ℝ)/2-4/((d+1)*δ)≤0 := by
    have hh : (1:ℝ)/2≤4/((d+1)*δ) :=
      (le_div_iff₀ hden).mpr (by linarith)
    linarith
  have hrc : d*(d-1)/2-4*d*(d-1)/((d+1)*δ)≤0 := by
    have hh := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hd0.le hdm.le) hbase
    convert hh using 1 <;> ring
  have hsc : -(d*(d-1)*(d-2)/((d+1)*δ))≤0 := by
    exact neg_nonpos.mpr (div_nonneg
      (mul_nonneg (mul_nonneg hd0.le hdm.le) (by linarith)) hden.le)
  have hq := mul_le_mul_of_nonpos_left hQ hqc
  have hr := mul_le_mul_of_nonpos_left hR hrc
  have hs := mul_le_mul_of_nonpos_left hS hsc
  have hid : (d-2*d/((d+1)*δ))*(8*E)+
      (d*(d-1)/2-4*d*(d-1)/((d+1)*δ))*(4*E)-
      (d*(d-1)*(d-2)/((d+1)*δ))*((4+8/(3*(d-1)))*E)=
      -(highLeading d/δ-highPositive d)*E := by
    unfold highLeading highPositive
    field_simp
    ring
  linarith

theorem pair_projection_noise_high
    {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U : Pair N→H) (W : H) (i : Fin N)
    {Q R S t β E : ℝ} (hN : 4≤N) (hGram : Gram U Q R S)
    (hConstant : ∀ e,inner ℝ W (U e)=t)
    (hβ1 : β<1) (hβhi : (N : ℝ)*(1-β)≤2)
    (hQ : Q≤8*E) (hR : R≤4*E) (hS : S≤(4+8/(3*((N : ℝ)-2)))*E) :
    β*‖W‖^2-(highLeading ((N : ℝ)-1)/(1-β)-
      highPositive ((N : ℝ)-1))*E≤covarianceNoiseForm W (star U i) ((N : ℝ)-1) Q := by
  have hNr : (4 : ℝ)≤N := by exact_mod_cast hN
  have hV : ‖star U i‖^2=((N : ℝ)-1)*Q+
      ((N : ℝ)-1)*(((N : ℝ)-1)-1)*R := by
    convert star_sq U hGram i using 1; ring
  have hP : ‖projection U‖^2=(2*((N : ℝ)-1)/(((N : ℝ)-1)+1))*
      (Q+2*(((N : ℝ)-1)-1)*R+
        ((((N : ℝ)-1)-1)*(((N : ℝ)-1)-2)/2)*S) := by
    convert projection_sq U hGram (by omega) using 1; unfold KLSBelow25.PairProjection.row; ring
  have hS' : S≤(4+8/(3*(((N : ℝ)-1)-1)))*E := by convert hS using 1; ring
  have hh := high_noise_bound_of_projection_data W (star U i) (projection U)
    (by linarith : 3≤(N : ℝ)-1) (by linarith : 0<1-β)
    (by convert hβhi using 1 <;> ring)
    (constant_pairing U W hConstant i) hV hP hQ hR hS'
  convert hh using 1; ring

theorem pair_projection_signed_noise_high
    {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U : Pair N → H) (W : H) (i : Fin N)
    {Q R S t β E γ : ℝ} (hN : 4 ≤ N) (hGram : Gram U Q R S)
    (hConstant : ∀ e, inner ℝ W (U e) = t)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hγ : 1 ≤ γ)
    (hhi : (N : ℝ)*(1-β) ≤ 2*γ^2)
    (hQ : Q ≤ 8*E) (hR : R ≤ 4*E) (hS : S ≤ (4+8/(3*((N : ℝ)-2)))*E) :
    β*‖W‖^2-(γ^2*highLeading ((N : ℝ)-1)/(1-β)-
      highPositive ((N : ℝ)-1))*E ≤
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
  have hb1 : b < 1 := by
    dsimp [b]
    exact sub_lt_self _ (div_pos (by linarith) hγs)
  have hbhi : (N : ℝ)*(1-b) ≤ 2 := by
    apply (mul_le_mul_iff_right₀ hγs).mp
    dsimp [b]
    field_simp
    nlinarith
  have hc : ∀ e, inner ℝ (γ • W) (U e) = γ*t := by
    intro e
    rw [real_inner_smul_left,hConstant]
  have hh := pair_projection_noise_high U (γ • W) i hN hGram hc hb1 hbhi hQ hR hS
  have hden : 1-b = (1-β)/γ^2 := by dsimp [b]; ring
  have hcoef : b*γ^2 = γ^2-1+β := by dsimp [b]; field_simp; ring
  have hnorm : ‖γ • W‖^2 = γ^2*‖W‖^2 := by
    rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  have hdiv : highLeading ((N : ℝ)-1)/(1-b) =
      γ^2*highLeading ((N : ℝ)-1)/(1-β) := by
    rw [hden]
    field_simp
  unfold covarianceNoiseForm at hh ⊢
  rw [hnorm,real_inner_smul_left,hdiv] at hh
  rw [←mul_assoc,hcoef] at hh
  nlinarith

variable {n r : ℕ}

theorem actual_all_rank_signed_pair_noise_high
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Tensor (ι := Fin n) (r+3)) (hT : Symmetric T)
    (W : Tensor (ι := Fin n) (r+4)) (hW : Symmetric W)
    {β γ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hγ : 1 ≤ γ)
    (hhi : ((r : ℝ)+4)*(1-β) ≤ 2*γ^2) :
    β*square W-(γ^2*highLeading ((r : ℝ)+3)/(1-β)-
      highPositive ((r : ℝ)+3))*square T ≤
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
  have hQcap : Q ≤ 8*square T := by
    simpa only [Q,e0,pairing,square,pow_two] using actual_pair_kernel_square_le_eight hμ T hT 0
  have hR : R ≤ 4*square T := actual_pair_kernel_cross_le_four hμ T hT 0 1
    (by norm_num [Fin.ext_iff])
  have hS : S ≤ (4+8/(3*(((r+4 : ℕ) : ℝ)-2)))*square T := by
    have hh := actual_pair_disjoint_le hμ T hT
    dsimp only [S,e0]
    convert hh using 1 <;> push_cast <;> ring_nf
  have hhi' : ((r+4 : ℕ) : ℝ)*(1-β) ≤ 2*γ^2 := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hhi
  have hh := pair_projection_signed_noise_high U (toHilbert W) (0 : Fin (r+4))
    (by omega) hg hc hβ0 hβ1 hγ hhi' hQcap hR hS
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

/-- A single coefficient valid in both parameter regions. -/
def signedNoiseLoss (d β γ : ℝ) : ℝ :=
  max (γ^2*leadingNoiseCoefficient d/(1-β)-positiveNoiseCoefficient d)
    (γ^2*highLeading d/(1-β)-highPositive d)

theorem actual_all_rank_signed_pair_noise_unrestricted
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Tensor (ι := Fin n) (r+3)) (hT : Symmetric T)
    (W : Tensor (ι := Fin n) (r+4)) (hW : Symmetric W)
    {β γ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hγ : 1 ≤ γ) :
    β*square W-signedNoiseLoss ((r : ℝ)+3) β γ*square T ≤
    (∑ i : Fin n, KLS.TensorEnergy.energyNoiseCorrection T
      (thirdCumulantMatrix μ (MomentMap.coordinateVector i))
      (fun a => W (Fin.cons i a)))-
      (4*(γ-1)/((r : ℝ)+4))*pairing W (creation (actualThirdCubicArray μ) T) := by
  have hE : 0 ≤ square T := Finset.sum_nonneg (fun a _ => sq_nonneg (T a))
  by_cases hlo : 2*γ^2 ≤ ((r : ℝ)+4)*(1-β)
  · have hh := actual_all_rank_signed_pair_noise hμ T hT W hW hβ0 hβ1 hγ hlo
    exact (sub_le_sub_left (mul_le_mul_of_nonneg_right
      (le_max_left _ _) hE) (β*square W)).trans hh
  · have hh := actual_all_rank_signed_pair_noise_high hμ T hT W hW hβ0 hβ1 hγ
      (le_of_lt (lt_of_not_ge hlo))
    exact (sub_le_sub_left (mul_le_mul_of_nonneg_right
      (le_max_right _ _) hE) (β*square W)).trans hh

end KLSConstantImprovement.SignedRowNoiseHigh
#print axioms KLSConstantImprovement.SignedRowNoiseHigh.high_noise_bound_of_projection_data
#print axioms KLSConstantImprovement.SignedRowNoiseHigh.actual_all_rank_signed_pair_noise_high
#print axioms KLSConstantImprovement.SignedRowNoiseHigh.actual_all_rank_signed_pair_noise_unrestricted

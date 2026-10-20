import KLSConstantImprovement.SignedRowNoiseHigh

/-! Reserving a positive diagonal covariance term in signed pair-noise control.
All parameters below are scalar; the Gram data are realized by actual laws. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators RealInnerProductSpace
namespace KLSConstantImprovement.SignedRowReservedNoise
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSBelow25.PairTensor KLSBelow25.PairProjection
open KLSConstantImprovement.SignedRowNoiseHigh
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

def lowRefund (d : ℝ) : ℝ := 4+8*(d-2)/(3*(d-1))

theorem reserved_low_noise_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (W V P : H) {d Q R S δ E κ : ℝ}
    (hd : 3≤d) (hδ : 0<δ) (hδ1 : δ≤1) (hκ : 0≤κ)
    (hδlo : 2*d≤(d+κ)*((d+1)*δ)) (hpay : (d+κ)*δ≤d)
    (hinner : inner ℝ W V=inner ℝ W P)
    (hV : ‖V‖^2=d*Q+d*(d-1)*R)
    (hP : ‖P‖^2=(2*d/(d+1))*(Q+2*(d-1)*R+((d-1)*(d-2)/2)*S))
    (hresidual : (d-2)*S≤Q+(d-3)*R)
    (hR : R≤4*E) (hS : S≤(4+8/(3*(d-1)))*E) :
    (1-δ)*‖W‖^2-(leadingNoiseCoefficient d/δ-positiveNoiseCoefficient d-
      κ*lowRefund d)*E≤covarianceNoiseForm W V d Q+κ*Q := by
  have hc := pair_noise_completion_of_projection_data W V P hd hδ hinner hV hP
  have hd0 : 0<d := by linarith
  have hdm : 0<d-1 := by linarith
  have hden : 0<(d+1)*δ := mul_pos (by linarith) hδ
  have ha : 0≤d-2*d/((d+1)*δ)+κ := by
    have hh := (div_le_iff₀ hden).mpr hδlo
    linarith
  have htwo : 2≤2/δ := (le_div_iff₀ hδ).mpr (by nlinarith)
  have hrc : d*(5-d)/2-2*d/δ-(d-3)*κ≤0 := by
    have hh : (5-d)/2-2/δ≤0 := by linarith
    have hh' := mul_nonpos_of_nonneg_of_nonpos hd0.le hh
    have hk := mul_nonneg (by linarith : 0≤d-3) hκ
    have hh2 : d*(5-d)/2-2*d/δ≤0 := by convert hh' using 1 <;> ring
    linarith
  have hp : d+κ≤d/δ := (le_div_iff₀ hδ).mpr hpay
  have hsc : d*(d-2)*(1-1/δ)+(d-2)*κ≤0 := by
    have hh := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0≤d-2)
      (by linarith : d+κ-d/δ≤0)
    convert hh using 1 <;> ring
  have hq0 : (d-2)*S-(d-3)*R≤Q := by linarith
  have hq := mul_le_mul_of_nonneg_left hq0 ha
  have hr := mul_le_mul_of_nonpos_left hR hrc
  have hs := mul_le_mul_of_nonpos_left hS hsc
  have hid : (d*(5-d)/2-2*d/δ-(d-3)*κ)*(4*E)+
      (d*(d-2)*(1-1/δ)+(d-2)*κ)*((4+8/(3*(d-1)))*E)=
      -(leadingNoiseCoefficient d/δ-positiveNoiseCoefficient d-κ*lowRefund d)*E := by
    unfold leadingNoiseCoefficient positiveNoiseCoefficient lowRefund
    field_simp
    ring
  have hcombine : (d*(5-d)/2-2*d/δ-(d-3)*κ)*R+
      (d*(d-2)*(1-1/δ)+(d-2)*κ)*S=
      (d-2*d/((d+1)*δ)+κ)*((d-2)*S-(d-3)*R)+
      (d*(d-1)/2-4*d*(d-1)/((d+1)*δ))*R-
      d*(d-1)*(d-2)/((d+1)*δ)*S := by
    field_simp
    ring
  nlinarith

theorem reserved_high_noise_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (W V P : H) {d Q R S δ E κ : ℝ}
    (hd : 3≤d) (hδ : 0<δ) (hκ : 0≤κ)
    (hδhi : (d+κ)*((d+1)*δ)≤2*d)
    (hinner : inner ℝ W V=inner ℝ W P)
    (hV : ‖V‖^2=d*Q+d*(d-1)*R)
    (hP : ‖P‖^2=(2*d/(d+1))*(Q+2*(d-1)*R+((d-1)*(d-2)/2)*S))
    (hQ : Q≤8*E) (hR : R≤4*E) (hS : S≤(4+8/(3*(d-1)))*E) :
    (1-δ)*‖W‖^2-(highLeading d/δ-highPositive d-8*κ)*E≤
      covarianceNoiseForm W V d Q+κ*Q := by
  have hc := pair_noise_completion_of_projection_data W V P hd hδ hinner hV hP
  have hd0 : 0<d := by linarith
  have hdm : 0<d-1 := by linarith
  have hden : 0<(d+1)*δ := mul_pos (by linarith) hδ
  have hdenhi : (d+1)*δ≤2 := by
    have hk := mul_nonneg hκ hden.le
    nlinarith
  have hqc : d-2*d/((d+1)*δ)+κ≤0 := by
    have hh := (le_div_iff₀ hden).mpr hδhi
    linarith
  have hbase : (1:ℝ)/2-4/((d+1)*δ)≤0 := by
    have hh : (1:ℝ)/2≤4/((d+1)*δ) := (le_div_iff₀ hden).mpr (by linarith)
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
  have hid : (d-2*d/((d+1)*δ)+κ)*(8*E)+
      (d*(d-1)/2-4*d*(d-1)/((d+1)*δ))*(4*E)-
      (d*(d-1)*(d-2)/((d+1)*δ))*((4+8/(3*(d-1)))*E)=
      -(highLeading d/δ-highPositive d-8*κ)*E := by
    unfold highLeading highPositive
    field_simp
    ring
  nlinarith

def reservedNoiseLoss (d β γ κ : ℝ) : ℝ :=
  max (γ^2*leadingNoiseCoefficient d/(1-β)-positiveNoiseCoefficient d-κ*lowRefund d)
    (γ^2*highLeading d/(1-β)-highPositive d-8*κ)

theorem pair_projection_signed_reserved_noise
    {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U : Pair N → H) (W : H) (i : Fin N)
    {Q R S t β E γ κ : ℝ} (hN : 4 ≤ N) (hGram : Gram U Q R S)
    (hConstant : ∀ e, inner ℝ W (U e) = t)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hγ : 1 ≤ γ) (hκ : 0 ≤ κ)
    (hpay : ((N : ℝ)-1+κ)*(1-β) ≤ ((N : ℝ)-1)*γ^2)
    (hE : 0≤E) (hQ : Q≤8*E) (hR : R≤4*E)
    (hS : S≤(4+8/(3*((N : ℝ)-2)))*E) :
    β*‖W‖^2-reservedNoiseLoss ((N : ℝ)-1) β γ κ*E ≤
    covarianceNoiseForm W (star U i) ((N : ℝ)-1) Q+κ*Q-
      2*(γ-1)*inner ℝ W (star U i) := by
  have hNr : (4 : ℝ)≤N := by exact_mod_cast hN
  have hγp : 0<γ := by linarith
  have hγs : 0<γ^2 := sq_pos_of_pos hγp
  have hγone : 1≤γ^2 := by nlinarith
  let δ : ℝ := (1-β)/γ^2
  have hδ : 0<δ := div_pos (by linarith) hγs
  have hδ1 : δ≤1 := (div_le_one hγs).mpr (by linarith)
  have hpay' : ((N : ℝ)-1+κ)*δ≤(N : ℝ)-1 := by
    dsimp [δ]
    rw [←mul_div_assoc]
    exact (div_le_iff₀ hγs).mpr hpay
  have hV : ‖star U i‖^2=((N : ℝ)-1)*Q+
      ((N : ℝ)-1)*(((N : ℝ)-1)-1)*R := by
    convert star_sq U hGram i using 1; ring
  have hP : ‖projection U‖^2=(2*((N : ℝ)-1)/(((N : ℝ)-1)+1))*
      (Q+2*(((N : ℝ)-1)-1)*R+
        ((((N : ℝ)-1)-1)*(((N : ℝ)-1)-2)/2)*S) := by
    convert projection_sq U hGram (by omega) using 1
    unfold KLSBelow25.PairProjection.row
    ring
  have hres : (((N : ℝ)-1)-2)*S≤Q+(((N : ℝ)-1)-3)*R := by
    convert residual_relation U hGram (by omega) using 1 <;> ring
  have hS' : S≤(4+8/(3*(((N : ℝ)-1)-1)))*E := by convert hS using 1; ring
  have hi : inner ℝ (γ • W) (star U i)=inner ℝ (γ • W) (projection U) := by
    rw [real_inner_smul_left,real_inner_smul_left,constant_pairing U W hConstant i]
  have hh : (1-δ)*‖γ • W‖^2-
      max (leadingNoiseCoefficient ((N : ℝ)-1)/δ-positiveNoiseCoefficient ((N : ℝ)-1)-κ*lowRefund ((N : ℝ)-1))
        (highLeading ((N : ℝ)-1)/δ-highPositive ((N : ℝ)-1)-8*κ)*E ≤
      covarianceNoiseForm (γ • W) (star U i) ((N : ℝ)-1) Q+κ*Q := by
    by_cases hlo : 2*((N : ℝ)-1)≤((N : ℝ)-1+κ)*((((N : ℝ)-1)+1)*δ)
    · have hl := reserved_low_noise_bound (γ • W) (star U i) (projection U)
        (by linarith : 3≤(N : ℝ)-1) hδ hδ1 hκ hlo hpay' hi hV hP hres hR hS'
      exact (sub_le_sub_left (mul_le_mul_of_nonneg_right (le_max_left _ _) hE) _).trans hl
    · have hl := reserved_high_noise_bound (γ • W) (star U i) (projection U)
        (by linarith : 3≤(N : ℝ)-1) hδ hκ (le_of_lt (lt_of_not_ge hlo)) hi hV hP hQ hR hS'
      exact (sub_le_sub_left (mul_le_mul_of_nonneg_right (le_max_right _ _) hE) _).trans hl
  have hc : (1-δ)*γ^2=γ^2-1+β := by dsimp [δ]; field_simp; ring
  have hn : ‖γ • W‖^2=γ^2*‖W‖^2 := by
    rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  have hd1 : leadingNoiseCoefficient ((N : ℝ)-1)/δ=
      γ^2*leadingNoiseCoefficient ((N : ℝ)-1)/(1-β) := by dsimp [δ]; field_simp
  have hd2 : highLeading ((N : ℝ)-1)/δ=
      γ^2*highLeading ((N : ℝ)-1)/(1-β) := by dsimp [δ]; field_simp
  unfold covarianceNoiseForm at hh ⊢
  rw [hn,real_inner_smul_left,hd1,hd2,←mul_assoc,hc] at hh
  unfold reservedNoiseLoss
  nlinarith

variable {n r : ℕ}

theorem actual_all_rank_signed_reserved_pair_noise
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Tensor (ι := Fin n) (r+3)) (hT : Symmetric T)
    (W : Tensor (ι := Fin n) (r+4)) (hW : Symmetric W)
    {β γ κ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hγ : 1 ≤ γ) (hκ : 0≤κ)
    (hpay : ((r : ℝ)+3+κ)*(1-β) ≤ ((r : ℝ)+3)*γ^2) :
    β*square W-reservedNoiseLoss ((r : ℝ)+3) β γ κ*square T ≤
    (∑ i : Fin n, KLS.TensorEnergy.energyNoiseCorrection T
      (thirdCumulantMatrix μ (MomentMap.coordinateVector i))
      (fun a => W (Fin.cons i a)))+
      κ*square (kernel (actualThirdCubicArray μ) T (incidentPair (0 : Fin (r+3))))-
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
  have hp' : (((r+4 : ℕ) : ℝ)-1+κ)*(1-β) ≤ (((r+4 : ℕ) : ℝ)-1)*γ^2 := by
    convert hpay using 1 <;> push_cast <;> ring
  have hE : 0 ≤ square T := Finset.sum_nonneg (fun a _ => sq_nonneg (T a))
  have hh := pair_projection_signed_reserved_noise U (toHilbert W) (0 : Fin (r+4))
    (by omega) hg hc hβ0 hβ1 hγ hκ hp' hE hQcap hR hS
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
  have hqeq : Q = square (kernel (actualThirdCubicArray μ) T (incidentPair (0 : Fin (r+3)))) := by
    simp only [Q,e0,pairing,square,pow_two]
  rw [hqeq] at hh
  convert hh using 1 <;> push_cast <;> ring

end KLSConstantImprovement.SignedRowReservedNoise
#print axioms KLSConstantImprovement.SignedRowReservedNoise.reserved_low_noise_bound
#print axioms KLSConstantImprovement.SignedRowReservedNoise.reserved_high_noise_bound
#print axioms KLSConstantImprovement.SignedRowReservedNoise.pair_projection_signed_reserved_noise
#print axioms KLSConstantImprovement.SignedRowReservedNoise.actual_all_rank_signed_reserved_pair_noise

import KLSConstantImprovement.RawCubicQuarticAffineFamily
import KLSConstantImprovement.RawCubicQuarticWeightedBudget

/-! Arbitrary-J affine cubic-to-quartic barriers. Three exact rational
square comparisons certify the endpoint u=1,Z=8 uniformly on the full
domain. The actual-law transfer is unchanged and supplies a same-test
support from the already proved universal cubic theorem. -/
noncomputable section
open MeasureTheory Set
namespace KLSConstantImprovement.RawCubicQuarticEndpointBarrier
open KLS KLS.DeterministicBridgeNext RawCubicQuarticTransfer
open RawCubicQuarticAffineFamily (phi phi_positive phi_deriv)
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

structure EndpointCertificate (H J s a b c : ℝ) : Prop where
  H_positive : 0 < H
  J_positive : 0 < J
  contact_unit : s ∈ Ioo (0 : ℝ) 1
  a_nonneg : 0 ≤ a
  b_nonneg : 0 ≤ b
  c_nonneg : 0 ≤ c
  a_square : 1536 ≤ a^2*H
  b_square : 704*H ≤ b^2*(J*(1-s))
  c_square : 442368 ≤ c^2*(J*(1-s))
  margin : 29+b+c < s*J/(2*H)-s/(1-s)*(56+a)

theorem scalar_criterion {H J s a b c u Z : ℝ}
    (h : EndpointCertificate H J s a b c)
    (hu : u ∈ Icc (0 : ℝ) 1) (hZ : Z ∈ Icc (0 : ℝ) 8) :
    (-deriv (phi s) u/phi s u)*
      ((1/2:ℝ)*J/H*phi s u-(44/(1-(1/2:ℝ))-32)*u-
        2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u) >
      29+2*(Real.sqrt (176*H*u)+Real.sqrt (13824*Z))/Real.sqrt (J*phi s u) := by
  have hs := h.contact_unit
  have hsp : 0 < 1-s := sub_pos.mpr hs.2
  have hp := phi_positive hs hu
  have hphi : 1-s ≤ phi s u := by
    dsimp [phi]
    nlinarith [mul_le_mul_of_nonneg_left hu.2 hs.1.le]
  have hbase : J*(1-s) ≤ J*phi s u := mul_le_mul_of_nonneg_left hphi h.J_positive.le
  have hsH : 0 < Real.sqrt H := Real.sqrt_pos.mpr h.H_positive
  have hsHsq := Real.sq_sqrt h.H_positive.le
  have hsZsq := Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤48) hZ.1)
  have hA : 2*Real.sqrt (48*Z) ≤ a*Real.sqrt H := by
    apply (sq_le_sq₀ (by positivity : 0≤2*Real.sqrt (48*Z))
      (mul_nonneg h.a_nonneg (Real.sqrt_nonneg H))).mp
    rw [mul_pow,mul_pow,hsZsq,hsHsq]
    nlinarith only [h.a_square,hZ.2]
  have hsu : Real.sqrt u ≤ 1 := by
    have hsq := Real.sq_sqrt hu.1
    have hn := Real.sqrt_nonneg u
    nlinarith only [hsq,hn,hu.2]
  have hcross : 2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u ≤ a := by
    have hd : 2*Real.sqrt (48*Z)/Real.sqrt H ≤ a := (div_le_iff₀ hsH).mpr hA
    calc
      _ ≤ a*Real.sqrt u := mul_le_mul_of_nonneg_right hd (Real.sqrt_nonneg u)
      _ ≤ a := by nlinarith only [hsu,h.a_nonneg]
  let q : ℝ := s/phi s u
  have hq0 : 0 ≤ q := (div_pos hs.1 hp).le
  have hqb : q ≤ s/(1-s) := div_le_div_of_nonneg_left hs.1.le hsp hphi
  have hpay : q*(56*u+2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u) ≤
      s/(1-s)*(56+a) := by
    have hS : 56*u+2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u ≤ 56+a := by
      linarith only [hu.2,hcross]
    exact (mul_le_mul_of_nonneg_left hS hq0).trans
      (mul_le_mul_of_nonneg_right hqb (by linarith only [h.a_nonneg]))
  have hlhs : s*J/(2*H)-s/(1-s)*(56+a) ≤
      q*((1/2:ℝ)*J/H*phi s u-56*u-
        2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u) := by
    have he : q*((1/2:ℝ)*J/H*phi s u-56*u-
        2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u) =
      s*J/(2*H)-q*(56*u+2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u) := by
      dsimp only [q]
      field_simp [hp.ne',h.H_positive.ne'] <;> ring
    rw [he]
    linarith only [hpay]
  have hd0 : 0 < Real.sqrt (J*phi s u) := Real.sqrt_pos.mpr (mul_pos h.J_positive hp)
  have hd := Real.sq_sqrt (mul_pos h.J_positive hp).le
  have ha := Real.sq_sqrt (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤176) h.H_positive.le) hu.1)
  have hc := Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤13824) hZ.1)
  have hpb : 704*H*u ≤ b^2*(J*phi s u) := by
    calc
      _ ≤ 704*H := by nlinarith only [mul_le_mul_of_nonneg_left hu.2 h.H_positive.le]
      _ ≤ b^2*(J*(1-s)) := h.b_square
      _ ≤ _ := mul_le_mul_of_nonneg_left hbase (sq_nonneg b)
  have hpc : 4*(13824*Z) ≤ c^2*(J*phi s u) := by
    calc
      _ ≤ 442368 := by nlinarith only [hZ.2]
      _ ≤ c^2*(J*(1-s)) := h.c_square
      _ ≤ _ := mul_le_mul_of_nonneg_left hbase (sq_nonneg c)
  have hB : 2*Real.sqrt (176*H*u) ≤ b*Real.sqrt (J*phi s u) := by
    apply (sq_le_sq₀ (by positivity : 0≤2*Real.sqrt (176*H*u))
      (mul_nonneg h.b_nonneg (Real.sqrt_nonneg (J*phi s u)))).mp
    rw [mul_pow,mul_pow,ha,hd]
    nlinarith only [hpb]
  have hC : 2*Real.sqrt (13824*Z) ≤ c*Real.sqrt (J*phi s u) := by
    apply (sq_le_sq₀ (by positivity : 0≤2*Real.sqrt (13824*Z))
      (mul_nonneg h.c_nonneg (Real.sqrt_nonneg (J*phi s u)))).mp
    rw [mul_pow,mul_pow,hc,hd]
    nlinarith only [hpc]
  have hbr : 2*Real.sqrt (176*H*u)/Real.sqrt (J*phi s u) ≤ b := (div_le_iff₀ hd0).mpr hB
  have hcr : 2*Real.sqrt (13824*Z)/Real.sqrt (J*phi s u) ≤ c := (div_le_iff₀ hd0).mpr hC
  rw [(phi_deriv s u).deriv]
  norm_num only [neg_neg,show (44/(1-(1/2:ℝ))-32)=56 by norm_num]
  change q*((1/2:ℝ)*J/H*phi s u-56*u-
    2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u) > _
  rw [mul_add,add_div]
  linarith only [hlhs,hbr,hcr,h.margin]

def barrier {H J s a b c : ℝ} (h : EndpointCertificate H J s a b c) :
    RawCubicQuarticBarrier H J where
  phi := phi s
  alpha := fun _ => 1/2
  continuous := by unfold phi; fun_prop
  positive := fun _ hu => phi_positive h.contact_unit hu
  antitone := by
    intro x hx y hy hxy
    dsimp [phi]
    nlinarith [mul_le_mul_of_nonneg_left hxy h.contact_unit.1.le]
  concave := by
    refine ⟨convex_Icc _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    dsimp [phi]
    nlinarith
  hasDeriv := fun u _ => by rw [(phi_deriv s u).deriv]; exact phi_deriv s u
  derivative_negative := fun u _ => by rw [(phi_deriv s u).deriv]; linarith [h.contact_unit.1]
  zero := by simp [phi]
  alpha_unit := fun _ _ => by norm_num
  alpha_ge_half := fun _ _ => le_refl _
  criterion := fun _ hu _ hZ => scalar_criterion h hu hZ

def slope (H J s : ℝ) : ℝ := J*s/(16*H)
def height (J : ℝ) : ℝ := J/576

theorem normalized_support {H J s a b c : ℝ}
    (h : EndpointCertificate H J s a b c)
    (hraw : RawCubicWeightedBudget.UniversalRawCubicBound H) :
    RawCubicQuarticWeightedBudget.UniversalCubicQuarticUnitSupport
      (slope H J s) (height J) := by
  intro n μ hμ f hf
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hb := actual_raw_cubic_quartic_joint_unit_bound h.H_positive hraw
    h.J_positive (barrier h) hμ f hf
  change actualAppellEnergy μ f 4 ≤ J*(1-s*(actualAppellEnergy μ f 3/H)) at hb
  have he : actualAppellEnergy μ f 4/576+
      slope H J s*(actualAppellEnergy μ f 3/36)-height J =
        (actualAppellEnergy μ f 4-J*(1-s*(actualAppellEnergy μ f 3/H)))/576 := by
    unfold slope height
    field_simp [h.H_positive.ne'] <;> ring
  apply sub_nonpos.mp
  rw [he]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hb) (by norm_num)

end KLSConstantImprovement.RawCubicQuarticEndpointBarrier
#print axioms KLSConstantImprovement.RawCubicQuarticEndpointBarrier.scalar_criterion
#print axioms KLSConstantImprovement.RawCubicQuarticEndpointBarrier.barrier
#print axioms KLSConstantImprovement.RawCubicQuarticEndpointBarrier.normalized_support

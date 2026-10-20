import KLSConstantImprovement.RawCubicQuarticTransfer

/-! Universal affine cubic-to-quartic supports for every proved prior H>=216.
The scalar criterion has a uniform strict margin; actual-law transfer uses
only the explicitly supplied original-class cubic theorem. -/
noncomputable section
open Set MeasureTheory
namespace KLSConstantImprovement.RawCubicQuarticAffineFamily
open KLS KLS.DeterministicBridgeNext RawCubicQuarticTransfer
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def phi (s u : ℝ) : ℝ := 1-s*u
def J (H s : ℝ) : ℝ := (8*H/3)*(44/(1-s)+27/s)

theorem phi_positive {s u : ℝ} (hs : s∈Ioo (0:ℝ) 1)
    (hu : u∈Icc (0:ℝ) 1) : 0<phi s u := by
  dsimp [phi]
  nlinarith [hs.2, mul_le_mul_of_nonneg_left hu.2 hs.1.le]

theorem J_positive {H s : ℝ} (hH : 0<H) (hs : s∈Ioo (0:ℝ) 1) : 0<J H s := by
  have hsp : 0<1-s := sub_pos.mpr hs.2
  unfold J
  exact mul_pos (by positivity) (add_pos (div_pos (by norm_num) hsp) (div_pos (by norm_num) hs.1))

theorem phi_deriv (s u : ℝ) : HasDerivAt (phi s) (-s) u := by
  convert (hasDerivAt_const u (1:ℝ)).sub ((hasDerivAt_id u).const_mul s) using 1 <;>
    first | (ext x; simp [phi]) | (simp <;> ring)

theorem scalar_criterion {H s u Z : ℝ} (hH : 216≤H)
    (hs : s∈Ioo (0:ℝ) 1) (hu : u∈Icc (0:ℝ) 1) (hZ : Z∈Icc (0:ℝ) 8) :
    (-deriv (phi s) u/phi s u)*
      ((1/2:ℝ)*J H s/H*phi s u-(44/(1-(1/2:ℝ))-32)*u-
        2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u) >
      29+2*(Real.sqrt (176*H*u)+Real.sqrt (13824*Z))/Real.sqrt (J H s*phi s u) := by
  have hHp : 0<H := by linarith
  have hsp : 0<1-s := sub_pos.mpr hs.2
  have hp := phi_positive hs hu
  have hJp := J_positive hHp hs
  have hphi : 1-s≤phi s u := by
    dsimp [phi]
    nlinarith [mul_le_mul_of_nonneg_left hu.2 hs.1.le]
  have hbase : (352/3:ℝ)*H ≤ J H s*phi s u := by
    have h := mul_le_mul_of_nonneg_left hphi hJp.le
    have hlow : (352/3:ℝ)*H ≤ J H s*(1-s) := by
      have hterm : 0≤(8*H/3)*(27/s)*(1-s) := mul_nonneg (mul_nonneg (by positivity) (div_nonneg (by norm_num) hs.1.le)) hsp.le
      have he : J H s*(1-s)=(352/3:ℝ)*H+(8*H/3)*(27/s)*(1-s) := by
        unfold J
        field_simp [hsp.ne']
        <;> ring
      rw [he]
      linarith only [hterm]
    exact hlow.trans h
  have hsH : 0<Real.sqrt H := Real.sqrt_pos.mpr hHp
  have hsHsq := Real.sq_sqrt hHp.le
  have hsZsq := Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤48) hZ.1)
  have hsZ0 := Real.sqrt_nonneg (48*Z)
  have hsZbound : 2*Real.sqrt (48*Z) ≤ (8/3:ℝ)*Real.sqrt H := by
    apply (sq_le_sq₀ (by positivity : 0≤2*Real.sqrt (48*Z)) (by positivity : 0≤(8/3:ℝ)*Real.sqrt H)).mp
    nlinarith only [hsZsq, hsHsq, hH, hZ.2]
  have hsu : Real.sqrt u≤1 := by
    have hh := Real.sq_sqrt hu.1
    have hh0 := Real.sqrt_nonneg u
    nlinarith [hu.2]
  have hcross0 : 0≤2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u := by positivity
  have hcross : 2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u≤(8/3:ℝ) := by
    have hdiv : 2*Real.sqrt (48*Z)/Real.sqrt H≤(8/3:ℝ) := (div_le_iff₀ hsH).mpr hsZbound
    calc
      _ ≤ (8/3:ℝ)*Real.sqrt u := mul_le_mul_of_nonneg_right hdiv (Real.sqrt_nonneg u)
      _ ≤ 8/3 := by linarith
  let q : ℝ := s/phi s u
  have hq0 : 0 ≤ q := (div_pos hs.1 hp).le
  have hqb : q ≤ s/(1-s) := div_le_div_of_nonneg_left hs.1.le hsp hphi
  have hpay : q*(56*u+2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u) ≤
      s/(1-s)*(176/3:ℝ) := by
    have hS : 56*u+2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u≤(176/3:ℝ) := by linarith [hu.2]
    exact (mul_le_mul_of_nonneg_left hS hq0).trans (mul_le_mul_of_nonneg_right hqb (by norm_num))
  have hidentity : s*J H s/(2*H)-s/(1-s)*(176/3:ℝ)=36 := by
    unfold J
    field_simp [hHp.ne',hs.1.ne',hsp.ne']
    <;> ring
  have hlhs : 36≤q*((1/2:ℝ)*J H s/H*phi s u-56*u-
      2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u) := by
    have he : q*((1/2:ℝ)*J H s/H*phi s u-56*u-
        2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u)=
      s*J H s/(2*H)-q*(56*u+2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u) := by
      dsimp [q]
      field_simp [hp.ne',hHp.ne']
      <;> ring
    rw [he]
    linarith only [hpay,hidentity]
  have hd0 : 0<Real.sqrt (J H s*phi s u) := Real.sqrt_pos.mpr (mul_pos hJp hp)
  have hd := Real.sq_sqrt (mul_pos hJp hp).le
  have ha0 := Real.sqrt_nonneg (176*H*u)
  have ha : (Real.sqrt (176*H*u))^2=176*H*u := Real.sq_sqrt (mul_nonneg (mul_nonneg (by norm_num) hHp.le) hu.1)
  have hb0 := Real.sqrt_nonneg (13824*Z)
  have hb : (Real.sqrt (13824*Z))^2=13824*Z := Real.sq_sqrt (mul_nonneg (by norm_num) hZ.1)
  have haBound : 2*Real.sqrt (176*H*u)≤(5/2:ℝ)*Real.sqrt (J H s*phi s u) := by
    have haUpper : 176*H*u≤176*H := by nlinarith [mul_le_mul_of_nonneg_left hu.2 hHp.le]
    apply (sq_le_sq₀ (by positivity : 0≤2*Real.sqrt (176*H*u)) (by positivity : 0≤(5/2:ℝ)*Real.sqrt (J H s*phi s u))).mp
    nlinarith only [ha,hd,hbase,haUpper,hHp.le]
  have hbBound : 2*Real.sqrt (13824*Z)≤(21/5:ℝ)*Real.sqrt (J H s*phi s u) := by
    apply (sq_le_sq₀ (by positivity : 0≤2*Real.sqrt (13824*Z)) (by positivity : 0≤(21/5:ℝ)*Real.sqrt (J H s*phi s u))).mp
    nlinarith only [hb,hd,hbase,hH,hZ.2]
  have haRatio : 2*Real.sqrt (176*H*u)/Real.sqrt (J H s*phi s u)≤(5/2:ℝ) :=
    (div_le_iff₀ hd0).mpr haBound
  have hbRatio : 2*Real.sqrt (13824*Z)/Real.sqrt (J H s*phi s u)≤(21/5:ℝ) :=
    (div_le_iff₀ hd0).mpr hbBound
  rw [(phi_deriv s u).deriv]
  norm_num only [neg_neg,show (44/(1-(1/2:ℝ))-32)=56 by norm_num]
  change q*((1/2:ℝ)*J H s/H*phi s u-56*u-
      2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u) > _
  rw [mul_add,add_div]
  linarith only [hlhs,haRatio,hbRatio]

def barrier {H s : ℝ} (hH : 216≤H) (hs : s∈Ioo (0:ℝ) 1) : RawCubicQuarticBarrier H (J H s) where
  phi := phi s
  alpha := fun _ => 1/2
  continuous := by unfold phi; fun_prop
  positive := fun _ hu => phi_positive hs hu
  antitone := by
    intro a ha b hb hab
    dsimp [phi]
    nlinarith [mul_le_mul_of_nonneg_left hab hs.1.le]
  concave := by
    refine ⟨convex_Icc _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    dsimp [phi]
    nlinarith
  hasDeriv := fun u _ => by rw [(phi_deriv s u).deriv]; exact phi_deriv s u
  derivative_negative := fun u _ => by rw [(phi_deriv s u).deriv]; linarith [hs.1]
  zero := by simp [phi]
  alpha_unit := fun _ _ => by norm_num
  alpha_ge_half := fun _ _ => le_refl _
  criterion := fun _ hu _ hZ => scalar_criterion hH hs hu hZ

end KLSConstantImprovement.RawCubicQuarticAffineFamily
#print axioms KLSConstantImprovement.RawCubicQuarticAffineFamily.scalar_criterion
#print axioms KLSConstantImprovement.RawCubicQuarticAffineFamily.barrier

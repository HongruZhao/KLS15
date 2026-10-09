import JointObservationScalarEndgame

/-! The first two actual observation caps are retained separately in the
adjoint-orbit argument. No law-specific assertion occurs in this module. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.CoupledEnergy
set_option maxHeartbeats 1500000

theorem two_head_weighted_prefix_le {p u v a b C P x y : ℝ}
    (hp : 0<p) (hpu : p≤u) (huv : u≤v)
    (hx : x≤a) (hy : y≤b) (hP : P≤C) :
    x/p+y/u+(P-x-y)/v≤a/p+b/u+(C-a-b)/v := by
  have hu : 0<u := hp.trans_le hpu
  have hv : 0<v := hu.trans_le huv
  have hpx : 0≤1/p-1/v := sub_nonneg.mpr ((one_div_le_one_div hv hp).mpr (hpu.trans huv))
  have huy : 0≤1/u-1/v := sub_nonneg.mpr ((one_div_le_one_div hv hu).mpr huv)
  have hx' := mul_le_mul_of_nonneg_right hx hpx
  have hy' := mul_le_mul_of_nonneg_right hy huy
  have hP' := div_le_div_of_nonneg_right hP hv.le
  have he (x y P : ℝ) : x/p+y/u+(P-x-y)/v=
      x*(1/p-1/v)+y*(1/u-1/v)+P/v := by ring
  rw [he,he]
  linarith

theorem normalized_orbit_le_of_two_head_caps
    (z c : ℕ → ℝ) {p u v r a b C : ℝ}
    (hp : 1<p) (ha : 0≤a) (hb : 0≤b) (hCab : a+b≤C)
    (hpu : p≤u) (huv : u≤v)
    (hu : u≤p^2-a) (hv : v≤u*(p-a/p)-b)
    (hr : 1<r) (hcost : r+a/p+b/u+(C-a-b)/v≤p)
    (hz0 : z 0=1) (hc : ∀ n,0≤c (n+1))
    (hcap1 : c 1≤a) (hcap2 : c 2≤b)
    (hbudget : ∀ n,prefixBudget c n≤C)
    (hrec : ∀ n,0<z n→0<z (n+1)→
      z (n+1)^2/z n-c (n+1)≤z (n+2))
    (henvelope : ∀ rho : ℝ,1<rho→∃ M : ℝ,∀ n,z n≤M*rho^n) :
    z 1≤p := by
  by_contra hnot
  have hz1p : p<z 1 := not_le.mp hnot
  have hp0 : 0<p := by linarith
  have hu0 : 0<u := hp0.trans_le hpu
  have hv0 : 0<v := hu0.trans_le huv
  have hz1 : 0<z 1 := hp0.trans hz1p
  have hq : r≤p-a/p-b/u := by
    have ht : 0≤(C-a-b)/v := div_nonneg (by linarith) hv0.le
    linarith
  have hq0 : 0<p-a/p := by
    have ht : 0≤b/u := div_nonneg hb hu0.le
    linarith
  have hc1div : c 1/z 1≤a/p := by
    exact (div_le_div_of_nonneg_right hcap1 hz1.le).trans
      (div_le_div_of_nonneg_left ha hp0 (le_of_lt hz1p))
  have hrec0 := hrec 0 (by simpa only [hz0] using (zero_lt_one : (0:ℝ)<1)) hz1
  rw [hz0,div_one] at hrec0
  have hz2u : u≤z 2 := by nlinarith [sq_nonneg (z 1-p)]
  have hz2 : 0<z 2 := hu0.trans_le hz2u
  have hratio2 : p-a/p≤z 2/z 1 := by
    apply (le_div_iff₀ hz1).mpr
    have hh := (div_le_iff₀ hz1).mp hc1div
    nlinarith
  have hrec1 := hrec 1 hz1 hz2
  have hz3v : v≤z 3 := by
    have hrmul := (le_div_iff₀ hz1).mp hratio2
    have he : z 2^2/z 1=(z 2/z 1)*z 2 := by ring
    rw [he] at hrec1
    have hh := mul_le_mul_of_nonneg_right hratio2 hz2.le
    have hh' := mul_le_mul_of_nonneg_left hz2u hq0.le
    nlinarith
  have hz3 : 0<z 3 := hv0.trans_le hz3v
  have ratio_rec (n : ℕ) (hn : 0<z n) (hn1 : 0<z (n+1)) :
      z (n+1)/z n-c (n+1)/z (n+1)≤z (n+2)/z (n+1) := by
    apply (le_div_iff₀ hn1).mpr
    have he : (z (n+1)/z n-c (n+1)/z (n+1))*z (n+1)=
        z (n+1)^2/z n-c (n+1) := by
      field_simp
    rw [he]
    exact hrec n hn hn1
  have hratio3 : z 1-c 1/z 1-c 2/z 2≤z 3/z 2 := by
    have hh : z 1-c 1/z 1≤z 2/z 1 := by
      have hh' := div_le_div_of_nonneg_right hrec0 hz1.le
      have he : (z 1^2-c 1)/z 1=z 1-c 1/z 1 := by
        field_simp
      rwa [he] at hh'
    linarith [ratio_rec 1 hz1 hz2]
  have hcostn (n : ℕ) :
      c 1/p+c 2/u+(prefixBudget c n-c 1-c 2)/v≤p-r := by
    have hh := two_head_weighted_prefix_le hp0 hpu huv hcap1 hcap2 (hbudget n)
    linarith
  have hinv : ∀ n : ℕ,
      0<z (n+2) ∧ v*r^n≤z (n+3) ∧
      z 1-c 1/z 1-c 2/z 2-
        (prefixBudget c (n+2)-c 1-c 2)/v≤z (n+3)/z (n+2) := by
    intro n
    induction n with
    | zero =>
      refine ⟨hz2,?_,?_⟩
      · simpa only [pow_zero,mul_one,Nat.zero_add] using hz3v
      · simpa [prefixBudget,Finset.sum_range_succ] using hratio3
    | succ n ih =>
      have hzn1 : 0<z (n+3) := lt_of_lt_of_le
        (mul_pos hv0 (pow_pos (by linarith) n)) ih.2.1
      have hzn1v : v≤z (n+3) := by
        have hpow : 1≤r^n := one_le_pow₀ (by linarith)
        nlinarith [ih.2.1]
      have hdrop : c (n+3)/z (n+3)≤c (n+3)/v :=
        div_le_div_of_nonneg_left (hc (n+2)) hv0 hzn1v
      have hnextRatio : z 1-c 1/z 1-c 2/z 2-
          (prefixBudget c (n+3)-c 1-c 2)/v≤z (n+4)/z (n+3) := by
        have hh := ratio_rec (n+2) ih.1 hzn1
        rw [show n+3=(n+2)+1 by omega,prefixBudget_succ]
        have hi' := ih.2.2
        simp only [Nat.add_assoc,Nat.reduceAdd,add_div,sub_div] at hh hi' ⊢
        linarith
      have hratio : r≤z (n+4)/z (n+3) := by
        have hc1p : c 1/z 1≤c 1/p :=
          div_le_div_of_nonneg_left (hc 0) hp0 hz1p.le
        have hc2u : c 2/z 2≤c 2/u :=
          div_le_div_of_nonneg_left (hc 1) hu0 hz2u
        linarith [hcostn (n+3)]
      have hgrow : v*r^(n+1)≤z (n+4) := by
        have hm := (le_div_iff₀ hzn1).mp hratio
        calc
          v*r^(n+1)=(v*r^n)*r := by rw [pow_succ];ring
          _≤z (n+3)*r := mul_le_mul_of_nonneg_right ih.2.1 (by linarith)
          _≤z (n+4) := by simpa only [mul_comm] using hm
      exact ⟨by simpa only [Nat.add_assoc] using hzn1,
        by simpa only [Nat.add_assoc] using hgrow,
        by simpa only [Nat.add_assoc] using hnextRatio⟩
  let rho : ℝ := (1+r)/2
  have hrho : 1<rho := by dsimp [rho]; linarith
  obtain ⟨M,hM⟩ := henvelope rho hrho
  have hgrow (n : ℕ) : r^n≤z (n+3)/v := by
    exact (le_div_iff₀ hv0).mpr (by simpa only [mul_comm] using (hinv n).2.1)
  have henv (n : ℕ) : z (n+3)/v≤(M*rho^3/v)*rho^n := by
    have hh := div_le_div_of_nonneg_right (hM (n+3)) hv0.le
    rw [pow_add] at hh
    convert hh using 1
    ring
  exact no_growth_above_exponential_envelope
    (by linarith : 0<rho) (by dsimp [rho]; linarith : rho<r) hgrow henv

theorem scalar_orbit_le_rate_mul_two_head_threshold
    (e bcost : ℕ → ℝ) {K C p u v r a b : ℝ}
    (hK : 0<K) (hp : 1<p) (ha : 0≤a) (hb : 0≤b) (hCab : a+b≤C)
    (hpu : p≤u) (huv : u≤v)
    (hu : u≤p^2-a) (hv : v≤u*(p-a/p)-b)
    (hr : 1<r) (hcost : r+a/p+b/u+(C-a-b)/v≤p)
    (he0 : e 0=1) (hbcost : ∀ n,0≤bcost (n+1))
    (hcap1 : K⁻¹^2*bcost 1≤a) (hcap2 : K⁻¹^3*bcost 2≤b)
    (hbudget : ∀ N,∑ m∈Finset.Icc 1 N,K⁻¹^(m+1)*bcost m≤C)
    (hrec : ∀ n,0<e n→0<e (n+1)→
      e (n+1)^2/e n-bcost (n+1)≤e (n+2))
    (henvelope : ∀ rho : ℝ,1<rho→∃ M : ℝ,∀ n,e n≤M*(K*rho)^n) :
    e 1≤K*p := by
  let z : ℕ → ℝ := fun n => e n/K^n
  let c : ℕ → ℝ := fun n => K⁻¹^(n+1)*bcost n
  have hz0 : z 0=1 := by simp [z,he0]
  have hc : ∀ n,0≤c (n+1) := by intro n; dsimp [c]; positivity [hbcost n]
  have hcBudget : ∀ n,prefixBudget c n≤C := by
    intro n
    rw [prefixBudget_eq_Icc]
    exact hbudget n
  have hzrec : ∀ n,0<z n → 0<z (n+1) →
      z (n+1)^2/z n-c (n+1)≤z (n+2) := by
    intro n hn hn1
    have hu : 0<e n := (div_pos_iff_of_pos_right (pow_pos hK n)).mp hn
    have hu1 : 0<e (n+1) := (div_pos_iff_of_pos_right (pow_pos hK (n+1))).mp hn1
    have hr := div_le_div_of_nonneg_right (hrec n hu hu1) (pow_nonneg hK.le (n+2))
    have he : (e (n+1)^2/e n-bcost (n+1))/K^(n+2)=z (n+1)^2/z n-c (n+1) := by
      dsimp [z,c]
      simp only [inv_pow,Nat.add_assoc,Nat.reduceAdd]
      rw [pow_add K n 2,pow_succ]
      field_simp [ne_of_gt hK,ne_of_gt hu]
      ring
    rw [he] at hr
    exact hr
  have hzenv : ∀ rho : ℝ,1<rho → ∃ M : ℝ,∀ n,z n≤M*rho^n := by
    intro rho hrho
    obtain ⟨M,hM⟩ := henvelope rho hrho
    refine ⟨M,fun n => ?_⟩
    have he := div_le_div_of_nonneg_right (hM n) (pow_nonneg hK.le n)
    have hid : M*(K*rho)^n/K^n=M*rho^n := by
      rw [mul_pow]
      field_simp
    rwa [hid] at he
  have hh := normalized_orbit_le_of_two_head_caps z c hp ha hb hCab hpu huv hu hv hr hcost
    hz0 hc (by simpa [c] using hcap1) (by simpa [c] using hcap2) hcBudget hzrec hzenv
  have hh' : e 1/K≤p := by simpa [z] using hh
  exact (div_le_iff₀ hK).mp hh' |>.trans_eq (mul_comm _ _)

end KLSBelow25.CoupledEnergy
#print axioms KLSBelow25.CoupledEnergy.normalized_orbit_le_of_two_head_caps

#print axioms KLSBelow25.CoupledEnergy.scalar_orbit_le_rate_mul_two_head_threshold

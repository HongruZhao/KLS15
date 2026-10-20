import TwoHeadObservationScalarEndgame

/-! A supporting line for the first two observations is spent jointly.
The individual caps are used only to initialize the first two orbit ratios. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.CoupledEnergy
set_option maxHeartbeats 1500000

theorem joint_two_head_weighted_prefix_le {p u v A B H C x y : ℝ}
    (_hv : 0<v) (hx : 0≤x) (hy : 0≤y)
    (hA : 1/p-1/v≤A) (hB : 1/u-1/v≤B)
    (hjoint : A*x+B*y≤H) :
    x/p+y/u+(C-x-y)/v≤H+C/v := by
  have hx' := mul_le_mul_of_nonneg_right hA hx
  have hy' := mul_le_mul_of_nonneg_right hB hy
  have he : x/p+y/u+(C-x-y)/v=
      (1/p-1/v)*x+(1/u-1/v)*y+C/v := by ring
  rw [he]
  linarith

theorem normalized_orbit_le_of_joint_two_head_cap
    (z c : ℕ → ℝ) {p u v r a b C A B H : ℝ}
    (hp : 1<p) (hpu : p≤u) (huv : u≤v)
    (hu : u≤p^2-a) (hv : v≤u*(p-a/p)-b)
    (hr : 1<r) (hA : 1/p-1/v≤A) (hB : 1/u-1/v≤B)
    (hcost : r+H+C/v≤p)
    (hz0 : z 0=1) (hc : ∀ n,0≤c (n+1))
    (hcap1 : c 1≤a) (hcap2 : c 2≤b)
    (hjoint : A*c 1+B*c 2≤H)
    (hbudget : ∀ n,prefixBudget c n≤C)
    (hrec : ∀ n,0<z n→0<z (n+1)→
      z (n+1)^2/z n-c (n+1)≤z (n+2))
    (henvelope : ∀ rho : ℝ,1<rho→∃ M : ℝ,∀ n,z n≤M*rho^n) :
    z 1≤p := by
  have hp0 : 0<p := by linarith
  have hu0 : 0<u := hp0.trans_le hpu
  have hv0 : 0<v := hu0.trans_le huv
  have hsum : c 1+c 2≤C := by
    simpa [prefixBudget,Finset.sum_range_succ] using hbudget 2
  have hu' : u≤p^2-c 1 := by linarith
  have hdiv := div_le_div_of_nonneg_right hcap1 hp0.le
  have hmul := mul_le_mul_of_nonneg_left hdiv hu0.le
  have hv' : v≤u*(p-c 1/p)-c 2 := by linarith
  have hspend := joint_two_head_weighted_prefix_le (C := C) hv0 (hc 0) (hc 1) hA hB hjoint
  apply normalized_orbit_le_of_two_head_caps z c hp (hc 0) (hc 1) hsum
    hpu huv hu' hv' hr (by linarith [hspend]) hz0 hc le_rfl le_rfl hbudget hrec henvelope

theorem scalar_orbit_le_rate_mul_joint_two_head_threshold
    (e bcost : ℕ → ℝ) {K C p u v r a b A B H : ℝ}
    (hK : 0<K) (hp : 1<p) (hpu : p≤u) (huv : u≤v)
    (hu : u≤p^2-a) (hv : v≤u*(p-a/p)-b)
    (hr : 1<r) (hA : 1/p-1/v≤A) (hB : 1/u-1/v≤B)
    (hcost : r+H+C/v≤p)
    (he0 : e 0=1) (hbcost : ∀ n,0≤bcost (n+1))
    (hcap1 : K⁻¹^2*bcost 1≤a) (hcap2 : K⁻¹^3*bcost 2≤b)
    (hjoint : A*(K⁻¹^2*bcost 1)+B*(K⁻¹^3*bcost 2)≤H)
    (hbudget : ∀ N,∑ m∈Finset.Icc 1 N,K⁻¹^(m+1)*bcost m≤C)
    (hrec : ∀ n,0<e n→0<e (n+1)→
      e (n+1)^2/e n-bcost (n+1)≤e (n+2))
    (henvelope : ∀ rho : ℝ,1<rho→∃ M : ℝ,∀ n,e n≤M*(K*rho)^n) :
    e 1≤K*p := by
  have hp0 : 0<p := by linarith
  have hu0 : 0<u := hp0.trans_le hpu
  have hv0 : 0<v := hu0.trans_le huv
  have hx : 0≤K⁻¹^2*bcost 1 := mul_nonneg (by positivity) (hbcost 0)
  have hy : 0≤K⁻¹^3*bcost 2 := mul_nonneg (by positivity) (hbcost 1)
  have hsum : K⁻¹^2*bcost 1+K⁻¹^3*bcost 2≤C := by
    have hh := hbudget 2
    norm_num [Finset.sum_Icc_succ_top] at hh
    simpa only [inv_pow] using hh
  have hu' : u≤p^2-K⁻¹^2*bcost 1 := by linarith
  have hdiv := div_le_div_of_nonneg_right hcap1 hp0.le
  have hmul := mul_le_mul_of_nonneg_left hdiv hu0.le
  have hv' : v≤u*(p-(K⁻¹^2*bcost 1)/p)-K⁻¹^3*bcost 2 := by linarith
  have hspend := joint_two_head_weighted_prefix_le (C := C) hv0 hx hy hA hB hjoint
  exact scalar_orbit_le_rate_mul_two_head_threshold e bcost hK hp hx hy hsum
    hpu huv hu' hv' hr (by linarith [hspend]) he0 hbcost le_rfl le_rfl hbudget hrec henvelope

end KLSBelow25.CoupledEnergy
#print axioms KLSBelow25.CoupledEnergy.normalized_orbit_le_of_joint_two_head_cap
#print axioms KLSBelow25.CoupledEnergy.scalar_orbit_le_rate_mul_joint_two_head_threshold

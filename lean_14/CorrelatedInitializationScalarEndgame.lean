import JointTwoHeadObservationScalarEndgame

/-! The exact first observation initializes the second orbit value before
the correlated first/second observation constraint initializes the third. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.CoupledEnergy
set_option maxHeartbeats 1500000

theorem normalized_orbit_le_of_correlated_initialization
    (z c : ℕ → ℝ) {p u v r a C A B D : ℝ}
    (hp : 1<p) (hpu : p≤u) (hu : u≤p^2-a) (hpv : p^2≤v)
    (hr : 1<r) (hA : 1/p-1/v≤A) (hB : 1/u-1/v≤B)
    (hcost : r+D+C/v≤p)
    (hz0 : z 0=1) (hc : ∀ n,0≤c (n+1)) (hcap1 : c 1≤a)
    (hinit : v≤(p^2-c 1)*(p-c 1/p)-c 2)
    (hjoint : A*c 1+B*c 2≤D)
    (hbudget : ∀ n,prefixBudget c n≤C)
    (hrec : ∀ n,0<z n→0<z (n+1)→
      z (n+1)^2/z n-c (n+1)≤z (n+2))
    (henvelope : ∀ rho : ℝ,1<rho→∃ M : ℝ,∀ n,z n≤M*rho^n) :
    z 1≤p := by
  have hp0 : 0<p := by linarith
  have hu0 : 0<u := hp0.trans_le hpu
  have hux : u≤p^2-c 1 := by linarith
  have hx0 : 0<p^2-c 1 := hu0.trans_le hux
  have hxv : p^2-c 1≤v := by linarith [hc 0]
  have hsum : c 1+c 2≤C := by
    simpa [prefixBudget,Finset.sum_range_succ] using hbudget 2
  have hrecip : 1/(p^2-c 1)≤1/u := (one_div_le_one_div hx0 hu0).mpr hux
  have hB' : 1/(p^2-c 1)-1/v≤B := (sub_le_sub_right hrecip _).trans hB
  have hspend := joint_two_head_weighted_prefix_le (C := C)
    (hx0.trans_le hxv) (hc 0) (hc 1) hA hB' hjoint
  exact normalized_orbit_le_of_two_head_caps z c hp (hc 0) (hc 1) hsum
    (hpu.trans hux) hxv le_rfl hinit hr (by linarith [hspend])
    hz0 hc le_rfl le_rfl hbudget hrec henvelope

theorem scalar_orbit_le_rate_mul_correlated_initialization_threshold
    (e bcost : ℕ → ℝ) {K C p u v r a A B D : ℝ}
    (hK : 0<K) (hp : 1<p) (hpu : p≤u) (hu : u≤p^2-a) (hpv : p^2≤v)
    (hr : 1<r) (hA : 1/p-1/v≤A) (hB : 1/u-1/v≤B)
    (hcost : r+D+C/v≤p)
    (he0 : e 0=1) (hbcost : ∀ n,0≤bcost (n+1))
    (hcap1 : K⁻¹^2*bcost 1≤a)
    (hinit : v≤(p^2-K⁻¹^2*bcost 1)*(p-(K⁻¹^2*bcost 1)/p)-K⁻¹^3*bcost 2)
    (hjoint : A*(K⁻¹^2*bcost 1)+B*(K⁻¹^3*bcost 2)≤D)
    (hbudget : ∀ N,∑ m∈Finset.Icc 1 N,K⁻¹^(m+1)*bcost m≤C)
    (hrec : ∀ n,0<e n→0<e (n+1)→
      e (n+1)^2/e n-bcost (n+1)≤e (n+2))
    (henvelope : ∀ rho : ℝ,1<rho→∃ M : ℝ,∀ n,e n≤M*(K*rho)^n) :
    e 1≤K*p := by
  have hp0 : 0<p := by linarith
  have hu0 : 0<u := hp0.trans_le hpu
  have hx : 0≤K⁻¹^2*bcost 1 := mul_nonneg (by positivity) (hbcost 0)
  have hy : 0≤K⁻¹^3*bcost 2 := mul_nonneg (by positivity) (hbcost 1)
  have hux : u≤p^2-K⁻¹^2*bcost 1 := by linarith
  have hx0 : 0<p^2-K⁻¹^2*bcost 1 := hu0.trans_le hux
  have hxv : p^2-K⁻¹^2*bcost 1≤v := by linarith
  have hsum : K⁻¹^2*bcost 1+K⁻¹^3*bcost 2≤C := by
    have hh := hbudget 2
    norm_num [Finset.sum_Icc_succ_top] at hh
    simpa only [inv_pow] using hh
  have hrecip : 1/(p^2-K⁻¹^2*bcost 1)≤1/u :=
    (one_div_le_one_div hx0 hu0).mpr hux
  have hB' : 1/(p^2-K⁻¹^2*bcost 1)-1/v≤B :=
    (sub_le_sub_right hrecip _).trans hB
  have hspend := joint_two_head_weighted_prefix_le (C := C)
    (hx0.trans_le hxv) hx hy hA hB' hjoint
  exact scalar_orbit_le_rate_mul_two_head_threshold e bcost hK hp hx hy hsum
    (hpu.trans hux) hxv le_rfl hinit hr (by linarith [hspend])
    he0 hbcost le_rfl le_rfl hbudget hrec henvelope

end KLSBelow25.CoupledEnergy
#print axioms KLSBelow25.CoupledEnergy.normalized_orbit_le_of_correlated_initialization
#print axioms KLSBelow25.CoupledEnergy.scalar_orbit_le_rate_mul_correlated_initialization_threshold

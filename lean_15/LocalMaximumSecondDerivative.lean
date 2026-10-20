import Mathlib

/-! The second derivative test is proved from actual derivative limits and
one-dimensional mean value, so it does not require a maximum-principle axiom. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace KLS.DeterministicBridgeNext
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 theorem second_derivative_nonpos_of_localMax {f : ℝ → ℝ} {d : ℝ}
    (hmax : IsLocalMax f 0)
    (hdiff : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ f t)
    (hsecond : HasDerivAt (deriv f) d 0) : d ≤ 0 := by
  by_contra hd
  have hdpos : 0 < d := lt_of_not_ge hd
  have hlim := hsecond.tendsto_slope_zero_right
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < deriv f t := by
    filter_upwards [hlim.eventually (Ioi_mem_nhds hdpos),self_mem_nhdsWithin] with t ht htr
    have htrpos : 0 < t := htr
    simp only [zero_add,hmax.deriv_eq_zero,sub_zero,smul_eq_mul] at ht
    exact pos_of_mul_pos_right ht (inv_nonneg.mpr htrpos.le)
  have hall : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ f t ∧ f t ≤ f 0 ∧
      (0 < t → 0 < deriv f t) := by
    filter_upwards [hdiff,hmax,eventually_nhdsWithin_iff.mp hpos] with t hdt hmt hpt
    exact ⟨hdt,hmt,hpt⟩
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp hall
  have hsmall (t : ℝ) (ht0 : 0 ≤ t) (htδ : t ≤ δ/2) : dist t 0 < δ := by
    rw [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg ht0]
    linarith
  have he : 0 < δ/2 := by linarith
  have hfc : ContinuousOn f (Icc 0 (δ/2)) := by
    intro t ht
    exact (hball (hsmall t ht.1 ht.2)).1.continuousAt.continuousWithinAt
  have hfd : DifferentiableOn ℝ f (Ioo 0 (δ/2)) := by
    intro t ht
    exact (hball (hsmall t ht.1.le ht.2.le)).1.differentiableWithinAt
  obtain ⟨c,hc,hce⟩ := exists_deriv_eq_slope f he hfc hfd
  have hcp := (hball (hsmall c hc.1.le hc.2.le)).2.2 hc.1
  have hep := (hball (hsmall (δ/2) he.le le_rfl)).2.1
  have hcn : deriv f c ≤ 0 := by
    rw [hce,sub_zero]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hep) he.le
  linarith

 theorem iteratedDeriv_two_nonpos_of_localMax {f : ℝ → ℝ}
    (hmax : IsLocalMax f 0) (hf : ContDiffAt ℝ 2 f 0) :
    iteratedDeriv 2 f 0 ≤ 0 := by
  have hdiff : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ f t := by
    filter_upwards [hf.eventually (by norm_num)] with t ht
    exact ht.differentiableAt (by norm_num)
  have hder : ContDiffAt ℝ 1 (deriv f) 0 := hf.derivWithin (by norm_num)
  have hsecond := hder.differentiableAt (by norm_num)
  have hs := second_derivative_nonpos_of_localMax hmax hdiff hsecond.hasDerivAt
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hs

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.second_derivative_nonpos_of_localMax
#print axioms KLS.DeterministicBridgeNext.iteratedDeriv_two_nonpos_of_localMax

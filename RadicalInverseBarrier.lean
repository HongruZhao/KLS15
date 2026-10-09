import RadicalPolynomialBarrierCalculus

/-! Turning actual polynomial signs into a C1 inverse-barrier package. -/
noncomputable section
open Set Filter
open scoped Topology
namespace KLSBelow25.RadicalBarrier
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def slope (v vp : ℝ → ℝ) (t : ℝ) : ℝ := v t+t*vp t
def concavity (v vp vpp : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(3*v t*vp t+t*((vp t)^2+v t*vpp t))
def parameterDerivative (v vp : ℝ → ℝ) (t : ℝ) : ℝ := -v t*slope v vp t

 theorem hasDerivAt_parameterDerivative {v vp vpp : ℝ → ℝ}
    (hd : ∀ t, HasDerivAt v (vp t) t) (hdp : ∀ t, HasDerivAt vp (vpp t) t) (t : ℝ) :
    HasDerivAt (parameterDerivative v vp) (concavity v vp vpp t) t := by
  have hs := (hd t).add ((hasDerivAt_id' t).mul (hdp t))
  have he := (hd t).neg.mul hs
  convert he using 1
  · rfl
  · simp only [concavity,one_mul,Pi.add_apply,Pi.mul_apply,Pi.neg_apply]
    ring

 theorem parameter_mem_interval {T z : ℝ} (hT : 0 < T) (hz : 1-T^2 ≤ z) :
    parameter z ∈ Icc (0 : ℝ) T := by
  refine ⟨Real.sqrt_nonneg _,?_⟩
  by_cases hp : 0 ≤ 1-z
  · have hs : (parameter z)^2=1-z := Real.sq_sqrt hp
    have ht : 0 ≤ parameter z := Real.sqrt_nonneg _
    nlinarith
  · rw [parameter,Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hp)]
    exact hT.le

 theorem parameterDerivative_monotone {v vp vpp : ℝ → ℝ} {T : ℝ}
    (hv : Continuous v) (hvp : Continuous vp)
    (hd : ∀ t, HasDerivAt v (vp t) t) (hdp : ∀ t, HasDerivAt vp (vpp t) t)
    (hc : ∀ t ∈ Icc (0 : ℝ) T, 0 < concavity v vp vpp t) :
    MonotoneOn (parameterDerivative v vp) (Icc (0 : ℝ) T) := by
  apply (strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_).monotoneOn
  · unfold parameterDerivative slope
    exact (hv.neg.mul (hv.add (continuous_id.mul hvp))).continuousOn
  · intro t ht
    rw [(hasDerivAt_parameterDerivative hd hdp t).deriv]
    exact hc t (interior_subset ht)

def toDescendingC1Barrier {v vp vpp : ℝ → ℝ} {T : ℝ}
    (hT : 0 < T) (hT1 : T < 1) (hv : Continuous v) (hvp : Continuous vp)
    (hd : ∀ t, HasDerivAt v (vp t) t) (hdp : ∀ t, HasDerivAt vp (vpp t) t)
    (hpos : ∀ t ∈ Icc (0 : ℝ) T, 0 < v t)
    (hslope : ∀ t ∈ Icc (0 : ℝ) T, 0 < slope v vp t)
    (hconc : ∀ t ∈ Icc (0 : ℝ) T, 0 < concavity v vp vpp t)
    (hend : 1 < T^2*(v T)^2) : DescendingC1Barrier where
  left := 1-T^2
  right := 2
  U := value v
  Up := derivative v vp
  left_positive := by nlinarith [sq_nonneg (T-1)]
  left_lt_one := by nlinarith [sq_pos_of_pos hT]
  one_lt_right := by norm_num
  continuous := by
    unfold value
    exact ((continuous_const.sub continuous_id).mul
      ((hv.comp continuous_parameter).pow 2)).continuousOn
  strictDerivative := fun z _ => hasStrictDerivAt_value hv hvp hd z
  derivative_negative := by
    intro z hz
    have ht := parameter_mem_interval hT hz.1.le
    simpa only [derivative,slope,neg_mul] using
      neg_neg_of_pos (mul_pos (hpos _ ht) (hslope _ ht))
  derivative_antitone := by
    intro z hz y hy hzy
    have htz := parameter_mem_interval hT hz.1
    have hty := parameter_mem_interval hT hy.1
    have htp : parameter y ≤ parameter z := Real.sqrt_le_sqrt (by linarith)
    exact parameterDerivative_monotone hv hvp hd hdp hconc hty htz htp
  zero := by simp [value,parameter]
  endpoint := by
    have he : parameter (1-T^2)=T := by
      unfold parameter
      rw [show 1-(1-T^2)=T^2 by ring,Real.sqrt_sq hT.le]
    simpa only [value,he,sub_sub_cancel] using hend

end KLSBelow25.RadicalBarrier
#print axioms KLSBelow25.RadicalBarrier.toDescendingC1Barrier

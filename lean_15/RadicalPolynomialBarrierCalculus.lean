import C1InverseBarrier

/-! The square-root parameterization is genuinely C1 at z=1. The vanished
linear factor cancels the square-root cusp; no fictitious derivative of the
square root at zero is used. -/
noncomputable section
open Set Filter
open scoped Topology
namespace KLSBelow25.RadicalBarrier
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def parameter (z : ℝ) : ℝ := Real.sqrt (1-z)
def value (v : ℝ → ℝ) (z : ℝ) : ℝ := (1-z)*(v (parameter z))^2
def derivative (v vp : ℝ → ℝ) (z : ℝ) : ℝ :=
  -v (parameter z)*(v (parameter z)+parameter z*vp (parameter z))

 theorem hasDerivAt_one_sub_mul_continuous {g : ℝ → ℝ} (hg : ContinuousAt g 1) :
    HasDerivAt (fun z => (1-z)*g z) (-g 1) 1 := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have ht : Tendsto (fun z => -g z) (𝓝[≠] (1 : ℝ)) (𝓝 (-g 1)) :=
    hg.neg.tendsto.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hzne : z ≠ (1 : ℝ) := by simpa using hz
  rw [slope_def_field]
  field_simp [sub_ne_zero.mpr hzne]
  <;> ring

 theorem continuous_parameter : Continuous parameter := by
  unfold parameter
  fun_prop

 theorem hasDerivAt_value_one {v : ℝ → ℝ} (hv : Continuous v) :
    HasDerivAt (value v) (derivative v (fun _ => 0) 1) 1 := by
  have hc : ContinuousAt (fun z => (v (parameter z))^2) 1 :=
    ((hv.comp continuous_parameter).pow 2).continuousAt
  convert hasDerivAt_one_sub_mul_continuous hc using 1
  · rfl
  · norm_num [derivative,parameter]
    ring

 theorem hasDerivAt_value_lt_one {v vp : ℝ → ℝ}
    (hd : ∀ t : ℝ, HasDerivAt v (vp t) t) {z : ℝ} (hz : z < 1) :
    HasDerivAt (value v) (derivative v vp z) z := by
  have hp : 0 < 1-z := sub_pos.mpr hz
  have ht : 0 < parameter z := Real.sqrt_pos.mpr hp
  have hlin : HasDerivAt (fun y : ℝ => 1-y) (-1) z := by
    convert (hasDerivAt_const z (1 : ℝ)).sub (hasDerivAt_id' z) using 1 <;> norm_num
  have hs : HasDerivAt parameter (-1/(2*parameter z)) z := by
    change HasDerivAt (fun y => Real.sqrt (1-y)) (-1/(2*Real.sqrt (1-z))) z
    exact hlin.sqrt hp.ne'
  have hv := (hd (parameter z)).comp z hs
  have he := hlin.mul (hv.pow 2)
  convert he using 1
  · rfl
  · have ht2 : (parameter z)^2=1-z := Real.sq_sqrt hp.le
    simp only [derivative,Pi.pow_apply,Function.comp_apply,
      Nat.cast_ofNat,show (2 : ℕ)-1=1 by decide,pow_one]
    field_simp [ht.ne']
    rw [← ht2]
    ring

 theorem hasDerivAt_value_gt_one {v vp : ℝ → ℝ} {z : ℝ} (hz : 1 < z) :
    HasDerivAt (value v) (derivative v vp z) z := by
  have hlin : HasDerivAt (fun y : ℝ => (1-y)*(v 0)^2) (-(v 0)^2) z := by
    convert ((hasDerivAt_const z (1 : ℝ)).sub (hasDerivAt_id' z)).mul_const ((v 0)^2) using 1 <;>
      norm_num
  have he : value v =ᶠ[𝓝 z] (fun y => (1-y)*(v 0)^2) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    change (1 : ℝ) < y at hy
    change (1-y)*(v (Real.sqrt (1-y)))^2=(1-y)*(v 0)^2
    rw [Real.sqrt_eq_zero_of_nonpos (by linarith : 1-y ≤ 0)]
  have hr := hlin.congr_of_eventuallyEq he
  convert hr using 1
  · norm_num [derivative,parameter,Real.sqrt_eq_zero_of_nonpos (by linarith : 1-z ≤ 0)]
    ring

 theorem hasDerivAt_value {v vp : ℝ → ℝ} (hv : Continuous v)
    (hd : ∀ t : ℝ, HasDerivAt v (vp t) t) (z : ℝ) :
    HasDerivAt (value v) (derivative v vp z) z := by
  rcases lt_trichotomy z 1 with hz | hz | hz
  · exact hasDerivAt_value_lt_one hd hz
  · subst z
    simpa [derivative,parameter] using hasDerivAt_value_one hv
  · exact hasDerivAt_value_gt_one hz

 theorem continuous_derivative {v vp : ℝ → ℝ} (hv : Continuous v) (hvp : Continuous vp) :
    Continuous (derivative v vp) := by
  unfold derivative
  exact (hv.comp continuous_parameter).neg.mul
    ((hv.comp continuous_parameter).add (continuous_parameter.mul (hvp.comp continuous_parameter)))

 theorem hasStrictDerivAt_value {v vp : ℝ → ℝ} (hv : Continuous v) (hvp : Continuous vp)
    (hd : ∀ t : ℝ, HasDerivAt v (vp t) t) (z : ℝ) :
    HasStrictDerivAt (value v) (derivative v vp z) z := by
  exact hasStrictDerivAt_of_hasDerivAt_of_continuousAt
    (Eventually.of_forall fun y => hasDerivAt_value hv hd y)
    (continuous_derivative hv hvp).continuousAt

end KLSBelow25.RadicalBarrier
#print axioms KLSBelow25.RadicalBarrier.hasStrictDerivAt_value

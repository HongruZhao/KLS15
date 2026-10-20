import KLSConstantImprovement.ActualHilbertWeakPassage405

/-! A genuine scalar L2 weak limit retains positive-part bounds.  This
will pass the actual local excess estimate without assuming strong
convergence of the inverse fields or its unbounded pointwise mass. -/
noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped Topology RealInnerProductSpace ENNReal
namespace KLSConstantImprovement.ActualWeakPositivePart405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {α : Type*} [MeasurableSpace α] {ν : Measure α}

private theorem inner_eq_integral (f g : Lp ℝ 2 ν) :
    inner ℝ f g = ∫ x, f x * g x ∂ν := by
  rw [L2.inner_def]
  congr 1
  funext x
  simp only [RCLike.inner_apply, conj_trivial, mul_comm]

theorem inner_self_posPart (f : Lp ℝ 2 ν) :
    inner ℝ f (Lp.posPart f) = ‖Lp.posPart f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_integral, inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_posPart f] with x hx
  rw [hx]
  by_cases h : 0 ≤ f x
  · rw [max_eq_left h]
  · rw [max_eq_right (le_of_not_ge h)]
    ring

theorem inner_nonnegative_test_le_posPart (f z : Lp ℝ 2 ν)
    (hz : ∀ᵐ x ∂ν, 0 ≤ z x) :
    inner ℝ f z ≤ inner ℝ (Lp.posPart f) z := by
  rw [inner_eq_integral, inner_eq_integral]
  apply integral_mono_ae ((Lp.memLp f).integrable_mul (Lp.memLp z))
    ((Lp.memLp (Lp.posPart f)).integrable_mul (Lp.memLp z))
  filter_upwards [Lp.coeFn_posPart f, hz] with x hx hy
  change f x * z x ≤ Lp.posPart f x * z x
  rw [hx]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) hy

theorem posPart_norm_le_of_weak_inner_tendsto
    {f : ℕ → Lp ℝ 2 ν} {u : Lp ℝ 2 ν} {C : ℝ}
    (hC : 0 ≤ C)
    (hb : ∀ᶠ k in atTop, ‖Lp.posPart (f k)‖ ≤ C)
    (hw : ∀ z : Lp ℝ 2 ν,
      Tendsto (fun k => inner ℝ (f k) z) atTop (𝓝 (inner ℝ u z))) :
    ‖Lp.posPart u‖ ≤ C := by
  let z := Lp.posPart u
  have hz : ∀ᵐ x ∂ν, 0 ≤ z x :=
    (Lp.coeFn_posPart u).mono fun x hx => by rw [hx]; exact le_max_right _ _
  have hbound : inner ℝ u z ≤ C * ‖z‖ := by
    apply le_of_tendsto (hw z)
    filter_upwards [hb] with k hk
    exact (inner_nonnegative_test_le_posPart (f k) z hz).trans
      ((real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hk (norm_nonneg z)))
  rw [inner_self_posPart] at hbound
  change ‖Lp.posPart u‖ ^ 2 ≤ C * ‖Lp.posPart u‖ at hbound
  by_cases hzero : ‖Lp.posPart u‖ = 0
  · rw [hzero]; exact hC
  have hp : 0 < ‖Lp.posPart u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
  nlinarith

theorem ae_nonpositive_of_weak_and_posPart_tendsto_zero
    {f : ℕ → Lp ℝ 2 ν} {u : Lp ℝ 2 ν}
    (hw : ∀ z : Lp ℝ 2 ν,
      Tendsto (fun k => inner ℝ (f k) z) atTop (𝓝 (inner ℝ u z)))
    (hz : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ‖Lp.posPart (f k)‖ ≤ ε) :
    ∀ᵐ x ∂ν, u x ≤ 0 := by
  have hzero : Lp.posPart u = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    apply le_of_forall_pos_le_add
    intro ε hε
    simpa only [zero_add] using posPart_norm_le_of_weak_inner_tendsto hε.le (hz ε hε) hw
  have hae := Lp.coeFn_posPart u
  have hzLp : ((Lp.posPart u : Lp ℝ 2 ν) : α → ℝ) =ᵐ[ν] (0 : α → ℝ) := by
    rw [hzero]
    exact Lp.coeFn_zero _ _ _
  filter_upwards [hae, hzLp] with x hx hy
  have hm : max (u x) 0 = 0 := hx.symm.trans hy
  exact (le_max_left (u x) 0).trans hm.le

end KLSConstantImprovement.ActualWeakPositivePart405
#print axioms KLSConstantImprovement.ActualWeakPositivePart405.inner_self_posPart
#print axioms KLSConstantImprovement.ActualWeakPositivePart405.inner_nonnegative_test_le_posPart
#print axioms KLSConstantImprovement.ActualWeakPositivePart405.posPart_norm_le_of_weak_inner_tendsto
#print axioms KLSConstantImprovement.ActualWeakPositivePart405.ae_nonpositive_of_weak_and_posPart_tendsto_zero

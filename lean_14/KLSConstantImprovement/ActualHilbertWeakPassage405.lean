import KLS.WeakGradientExtraction

/-! Concrete Hilbert weak-limit facts used in the actual metric limit. -/
noncomputable section
open Filter InnerProductSpace
open scoped Topology RealInnerProductSpace
namespace KLSConstantImprovement.ActualHilbertWeakPassage405
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_le_of_weak_inner_tendsto {x : ℕ → E} {u : E} {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ k, ‖x k‖ ≤ M)
    (hw : ∀ y : E, Tendsto (fun k => inner ℝ (x k) y) atTop (𝓝 (inner ℝ u y))) :
    ‖u‖ ≤ M := by
  have hh : inner ℝ u u ≤ M * ‖u‖ :=
    le_of_tendsto (hw u) (Eventually.of_forall fun k =>
      (real_inner_le_norm (x k) u).trans (mul_le_mul_of_nonneg_right (hb k) (norm_nonneg u)))
  rw [real_inner_self_eq_norm_sq] at hh
  by_cases hu : ‖u‖ = 0
  · rw [hu]; exact hM
  have hup : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg u) (Ne.symm hu)
  nlinarith

theorem inner_tendsto_of_weak_and_strong {x z : ℕ → E} {u v : E} {M : ℝ}
    (hb : ∀ k, ‖x k‖ ≤ M)
    (hw : ∀ y : E, Tendsto (fun k => inner ℝ (x k) y) atTop (𝓝 (inner ℝ u y)))
    (hz : Tendsto z atTop (𝓝 v)) :
    Tendsto (fun k => inner ℝ (x k) (z k)) atTop (𝓝 (inner ℝ u v)) := by
  have hnorm : Tendsto (fun k => ‖z k - v‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hz
  have he : Tendsto (fun k => inner ℝ (x k) (z k - v)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun k => norm_nonneg _) (fun k => ?_)
      (show Tendsto (fun k => M * ‖z k - v‖) atTop (𝓝 0) by simpa only [mul_zero] using hnorm.const_mul M)
    exact (norm_inner_le_norm (x k) (z k - v)).trans
      (mul_le_mul_of_nonneg_right (hb k) (norm_nonneg _))
  have ht := (hw v).add he
  have heq (k : ℕ) : inner ℝ (x k) v + inner ℝ (x k) (z k - v) = inner ℝ (x k) (z k) := by
    rw [inner_sub_right]
    ring
  simpa only [add_zero] using ht.congr heq

end KLSConstantImprovement.ActualHilbertWeakPassage405
#print axioms KLSConstantImprovement.ActualHilbertWeakPassage405.norm_le_of_weak_inner_tendsto
#print axioms KLSConstantImprovement.ActualHilbertWeakPassage405.inner_tendsto_of_weak_and_strong

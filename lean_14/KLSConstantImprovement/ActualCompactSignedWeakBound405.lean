import KLSConstantImprovement.ActualCompactDensityHalf405

/-! The literal signed coordinate excess bound passes through weak L2
convergence on every compact set.  Both signs and the actual square-root
density are retained.  The vanishing excess is an explicit input here,
to be supplied by the actual target cutoff and local Kato estimate. -/
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ENNReal
namespace KLSConstantImprovement.ActualCompactSignedWeakBound405
open KLS ActualDensityWeightedL2405 ActualCompactDensityHalf405 ActualWeakPositivePart405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ}

def signedCompactResidual (φ : Space n → ℝ) (hφ : Continuous φ)
    (E : Set (Space n)) (hE : IsCompact E)
    (f : Lp ℝ 2 (volume : Measure (Space n))) (s B : ℝ) :
    Lp ℝ 2 (volume : Measure (Space n)) :=
  s • maskLp E hE.measurableSet f - B • compactDensityHalf φ hφ E hE

theorem signedCompactResidual_ae (φ : Space n → ℝ) (hφ : Continuous φ)
    (E : Set (Space n)) (hE : IsCompact E)
    (f : Lp ℝ 2 (volume : Measure (Space n))) (s B : ℝ) :
    (signedCompactResidual φ hφ E hE f s B : Space n → ℝ) =ᵐ[volume]
      E.indicator (fun x => s * f x - B * densityHalf φ x) := by
  filter_upwards [Lp.coeFn_sub (s • maskLp E hE.measurableSet f)
    (B • compactDensityHalf φ hφ E hE),
    Lp.coeFn_smul s (maskLp E hE.measurableSet f),
    Lp.coeFn_smul B (compactDensityHalf φ hφ E hE),
    maskLp_ae E hE.measurableSet f, compactDensityHalf_ae φ hφ E hE]
    with x hsub hs hB hf hρ
  change _ = _
  rw [signedCompactResidual, hsub]
  simp only [Pi.sub_apply]
  rw [hs, hB]
  change s * maskLp E hE.measurableSet f x - B * compactDensityHalf φ hφ E hE x = _
  rw [hf, hρ]
  by_cases hx : x ∈ E
  · simp only [indicator_of_mem hx]
  · simp only [indicator_of_notMem hx, mul_zero, sub_zero]

theorem signedCompactResidual_weak_tendsto
    {φ : ℕ → Space n → ℝ} {φ₀ : Space n → ℝ}
    (hφ : ∀ k, Continuous (φ k)) (hφ₀ : Continuous φ₀)
    (hlim : ∀ x, Tendsto (fun k => φ k x) atTop (𝓝 (φ₀ x)))
    {A : ℝ} (ha : ∀ k x, A ≤ φ k x)
    (E : Set (Space n)) (hE : IsCompact E)
    {f : ℕ → Lp ℝ 2 (volume : Measure (Space n))}
    {u : Lp ℝ 2 (volume : Measure (Space n))}
    (hw : ∀ z, Tendsto (fun k => inner ℝ (f k) z) atTop (𝓝 (inner ℝ u z)))
    (s B : ℝ) :
    ∀ z, Tendsto (fun k => inner ℝ (signedCompactResidual (φ k) (hφ k) E hE (f k) s B) z)
      atTop (𝓝 (inner ℝ (signedCompactResidual φ₀ hφ₀ E hE u s B) z)) := by
  intro z
  have hmask := maskLp_weak_tendsto E hE.measurableSet hw z
  have hρ : Tendsto (fun k => inner ℝ (compactDensityHalf (φ k) (hφ k) E hE) z)
      atTop (𝓝 (inner ℝ (compactDensityHalf φ₀ hφ₀ E hE) z)) :=
    (compact_densityHalf_tendsto_L2 hφ hφ₀ hlim ha E hE).inner
      (tendsto_const_nhds (x := z))
  simpa only [signedCompactResidual, inner_sub_left, real_inner_smul_left] using
    (hmask.const_mul s).sub (hρ.const_mul B)

theorem ae_abs_le_of_compact_signed_excess
    {φ : ℕ → Space n → ℝ} {φ₀ : Space n → ℝ}
    (hφ : ∀ k, Continuous (φ k)) (hφ₀ : Continuous φ₀)
    (hlim : ∀ x, Tendsto (fun k => φ k x) atTop (𝓝 (φ₀ x)))
    {A B : ℝ} (ha : ∀ k x, A ≤ φ k x)
    {f : ℕ → Lp ℝ 2 (volume : Measure (Space n))}
    {u : Lp ℝ 2 (volume : Measure (Space n))}
    (hw : ∀ z, Tendsto (fun k => inner ℝ (f k) z) atTop (𝓝 (inner ℝ u z)))
    (hexcess : ∀ m : ℕ, ∀ s : ℝ, (s = 1 ∨ s = -1) → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k in atTop, ‖Lp.posPart (signedCompactResidual (φ k) (hφ k)
        (Metric.closedBall (0 : Space n) (m : ℝ)) (isCompact_closedBall _ _) (f k) s B)‖ ≤ ε) :
    ∀ᵐ x ∂(volume : Measure (Space n)), |u x| ≤ B * densityHalf φ₀ x := by
  have hlocal (m : ℕ) (s : ℝ) (hs : s = 1 ∨ s = -1) :
      ∀ᵐ x ∂(volume : Measure (Space n)), x ∈ Metric.closedBall (0 : Space n) (m : ℝ) →
        s * u x ≤ B * densityHalf φ₀ x := by
    let E := Metric.closedBall (0 : Space n) (m : ℝ)
    have hE : IsCompact E := isCompact_closedBall _ _
    have hz := ae_nonpositive_of_weak_and_posPart_tendsto_zero
      (signedCompactResidual_weak_tendsto hφ hφ₀ hlim ha E hE hw s B) (hexcess m s hs)
    filter_upwards [hz, signedCompactResidual_ae φ₀ hφ₀ E hE u s B] with x hx he
    intro hxE
    rw [he, indicator_of_mem hxE] at hx
    linarith
  have hab (m : ℕ) : ∀ᵐ x ∂(volume : Measure (Space n)),
      x ∈ Metric.closedBall (0 : Space n) (m : ℝ) → |u x| ≤ B * densityHalf φ₀ x := by
    filter_upwards [hlocal m 1 (Or.inl rfl), hlocal m (-1) (Or.inr rfl)] with x hp hn
    intro hx
    have hp' := hp hx
    have hn' := hn hx
    exact abs_le.mpr ⟨by linarith, by simpa only [one_mul] using hp'⟩
  filter_upwards [ae_all_iff.mpr hab] with x hx
  obtain ⟨m, hm⟩ := exists_nat_ge ‖x‖
  apply hx m
  simpa only [Metric.mem_closedBall, dist_zero_right] using hm

end KLSConstantImprovement.ActualCompactSignedWeakBound405
#print axioms KLSConstantImprovement.ActualCompactSignedWeakBound405.signedCompactResidual_ae
#print axioms KLSConstantImprovement.ActualCompactSignedWeakBound405.signedCompactResidual_weak_tendsto
#print axioms KLSConstantImprovement.ActualCompactSignedWeakBound405.ae_abs_le_of_compact_signed_excess

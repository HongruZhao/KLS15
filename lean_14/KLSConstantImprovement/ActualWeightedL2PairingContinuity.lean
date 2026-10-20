import KLS.WeightedCompactSmoothing

/-! Actual weighted L2 pairing continuity used by the raw H1 vector passage. -/
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ENNReal
namespace KLSConstantImprovement.ActualWeightedL2PairingContinuity
open KLS
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem tendsto_integral_mul_of_weighted_L2
    {f g : ℕ → Space n → ℝ} {u v : Space n → ℝ}
    (hf : ∀ k, MemLp (f k) 2 μ) (hg : ∀ k, MemLp (g k) 2 μ)
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ)
    (hfu : Tendsto (fun k => eLpNorm (f k - u) 2 μ) atTop (𝓝 0))
    (hgv : Tendsto (fun k => eLpNorm (g k - v) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, f k x * g k x ∂μ) atTop (𝓝 (∫ x, u x * v x ∂μ)) := by
  have hF := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u hu).mpr hfu
  have hG := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hg v hv).mpr hgv
  have hi : Tendsto (fun k => inner ℝ ((hf k).toLp (f k)) ((hg k).toLp (g k)))
      atTop (𝓝 (inner ℝ (hu.toLp u) (hv.toLp v))) := hF.inner hG
  convert hi using 1
  · funext k
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hf k).coeFn_toLp, (hg k).coeFn_toLp] with x hx hy
    simp [hx, hy, mul_comm]
  · rw [L2.inner_def]
    congr 1
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x hx hy
    simp [hx, hy, mul_comm]

theorem weighted_L2_sub_tendsto
    {f g : ℕ → Space n → ℝ} {u v : Space n → ℝ}
    (hf : ∀ k, MemLp (f k) 2 μ) (hg : ∀ k, MemLp (g k) 2 μ)
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ)
    (hfu : Tendsto (fun k => eLpNorm (f k - u) 2 μ) atTop (𝓝 0))
    (hgv : Tendsto (fun k => eLpNorm (g k - v) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm ((f k - g k) - (u - v)) 2 μ) atTop (𝓝 0) := by
  have hF := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u hu).mpr hfu
  have hG := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hg v hv).mpr hgv
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun k => f k - g k) (fun k => (hf k).sub (hg k)) (u - v) (hu.sub hv)).mp
  change Tendsto (fun k => (hf k).toLp (f k) - (hg k).toLp (g k))
    atTop (𝓝 (hu.toLp u - hv.toLp v))
  exact hF.sub hG

theorem weighted_L2_add_tendsto
    {f g : ℕ → Space n → ℝ} {u v : Space n → ℝ}
    (hf : ∀ k, MemLp (f k) 2 μ) (hg : ∀ k, MemLp (g k) 2 μ)
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ)
    (hfu : Tendsto (fun k => eLpNorm (f k - u) 2 μ) atTop (𝓝 0))
    (hgv : Tendsto (fun k => eLpNorm (g k - v) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm ((f k + g k) - (u + v)) 2 μ) atTop (𝓝 0) := by
  have hF := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u hu).mpr hfu
  have hG := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hg v hv).mpr hgv
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun k => f k + g k) (fun k => (hf k).add (hg k)) (u + v) (hu.add hv)).mp
  change Tendsto (fun k => (hf k).toLp (f k) + (hg k).toLp (g k))
    atTop (𝓝 (hu.toLp u + hv.toLp v))
  exact hF.add hG

/-- Multiplication by an actual essentially bounded measurable coefficient
preserves strong weighted L2 convergence. No continuity of the coefficient
is imposed, so the actual almost-everywhere Hessian is covered. -/
theorem weighted_L2_bounded_mul_tendsto
    {c : Space n → ℝ} (hc : MemLp c ∞ μ)
    {f : ℕ → Space n → ℝ} {u : Space n → ℝ}
    (hf : ∀ k, MemLp (f k) 2 μ) (hu : MemLp u 2 μ)
    (hfu : Tendsto (fun k => eLpNorm (f k - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm
      ((fun x => c x * f k x) - (fun x => c x * u x)) 2 μ) atTop (𝓝 0) := by
  have he (k : ℕ) : ((fun x => c x * f k x) - (fun x => c x * u x)) =
      c * (f k - u) := by
    funext x
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring
  simp_rw [he]
  have hb (k : ℕ) : eLpNorm (c * (f k - u)) 2 μ ≤
      eLpNorm c ∞ μ * eLpNorm (f k - u) 2 μ :=
    eLpNorm_smul_le_mul_eLpNorm hc.aestronglyMeasurable
      ((hf k).sub hu).aestronglyMeasurable
  have ht : Tendsto (fun k => eLpNorm c ∞ μ * eLpNorm (f k - u) 2 μ)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hfu (Or.inr hc.eLpNorm_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => bot_le) hb

end KLSConstantImprovement.ActualWeightedL2PairingContinuity
#print axioms KLSConstantImprovement.ActualWeightedL2PairingContinuity.tendsto_integral_mul_of_weighted_L2
#print axioms KLSConstantImprovement.ActualWeightedL2PairingContinuity.weighted_L2_sub_tendsto
#print axioms KLSConstantImprovement.ActualWeightedL2PairingContinuity.weighted_L2_add_tendsto
#print axioms KLSConstantImprovement.ActualWeightedL2PairingContinuity.weighted_L2_bounded_mul_tendsto

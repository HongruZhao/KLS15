import FirstOrderMatrixCalculus

/-! Strong weighted L² smoothing for compact elements of the actual
maximal first-order matrix domain, including continuous drift terms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter Metric
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ} {ι ρ : Type*} [Fintype ι] [Fintype ρ]
  [DecidableEq ι] [DecidableEq ρ]

theorem eLpNorm_compact_mollify_sub_potential_tendsto_zero
    {φ f : Space n → ℝ} (hφ : Continuous φ)
    (hf : MemLp f 2 (potentialMeasure φ)) (hc : HasCompactSupport f) :
    Tendsto (fun k => eLpNorm (mollify k f - f) 2 (potentialMeasure φ)) atTop (𝓝 0) := by
  have hfV := memLp_volume_of_potentialMeasure_hasCompactSupport hf hφ hc
  have hm (k : ℕ) := memLp_of_continuous_hasCompactSupport hφ
    (mollify_contDiff (hfV.locallyIntegrable (by norm_num)) k).continuous
    (hasCompactSupport_mollify hc k)
  exact eLpNorm_potentialMeasure_sub_tendsto_zero_of_compact_support hφ
    (isCompact_mollifierEnlargement hc) (tsupport_mollify_subset hc)
    (subset_mollifierEnlargement _) (fun k => memLp_mollify hfV k) hfV hm hf
    (eLpNorm_mollify_sub_tendsto_zero hfV)

/-- A continuous, possibly globally unbounded drift coefficient commutes
with the strong compact approximation in the required weighted L² limit. -/
theorem eLpNorm_continuous_mul_compact_mollify_sub_potential_tendsto_zero
    {φ f b : Space n → ℝ} (hφ : Continuous φ) (hb : Continuous b)
    (hf : MemLp f 2 (potentialMeasure φ)) (hc : HasCompactSupport f) :
    Tendsto (fun k => eLpNorm (fun x => b x * mollify k f x - b x * f x)
      2 (potentialMeasure φ)) atTop (𝓝 0) := by
  let K := mollifierEnlargement (tsupport f)
  have hK : IsCompact K := isCompact_mollifierEnlargement hc
  obtain ⟨R, hR, hRK⟩ := hK.isBounded.subset_ball_lt 0 (0 : Space n)
  let η : ContDiffBump (0 : Space n) := ⟨R, R + 1, hR, by linarith⟩
  have hη (x : Space n) (hx : x ∈ K) : η x = 1 :=
    η.one_of_mem_closedBall (ball_subset_closedBall (hRK hx))
  have ht := eLpNorm_compact_mul_mollify_sub_potential_tendsto_zero hφ
    (hb.mul η.continuous) η.hasCompactSupport.mul_left
    (fun L hL => KLS.MemLp.restrict_volume_of_potentialMeasure hf hφ hL)
  convert ht using 1
  funext k
  congr 1
  funext x
  simp only [Pi.mul_apply]
  by_cases hx : x ∈ K
  · rw [hη x hx]
    simp only [mul_one]
  · have hm : mollify k f x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun he => hx (tsupport_mollify_subset hc k he))
    have hfx : f x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun he => hx (subset_mollifierEnlargement _ he))
    simp only [hm, hfx, mul_zero, sub_self]

theorem HasWeakMatrixDerivative.compact_smoothing
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {A : ρ → Fin n → ι → ℝ} {f : ι → Space n → ℝ} {g : ρ → Space n → ℝ}
    (h : HasWeakMatrixDerivative A f g)
    (hf : ∀ j, MemLp (f j) 2 (potentialMeasure φ))
    (hfc : ∀ j, HasCompactSupport (f j))
    (hg : ∀ a, MemLp (g a) 2 (potentialMeasure φ))
    (hgc : ∀ a, HasCompactSupport (g a)) (a : ρ) :
    Tendsto (fun k => eLpNorm
      (fun x => matrixDifferential A (fun j => mollify k (f j)) a x - g a x)
        2 (potentialMeasure φ)) atTop (𝓝 0) := by
  have hfloc (j : ι) :=
    (memLp_volume_of_potentialMeasure_hasCompactSupport (hf j) hφ (hfc j)).locallyIntegrable (by norm_num)
  have hgloc (a : ρ) :=
    (memLp_volume_of_potentialMeasure_hasCompactSupport (hg a) hφ (hgc a)).locallyIntegrable (by norm_num)
  simp_rw [h.mollify_eq hfloc hgloc]
  change Tendsto (fun k => eLpNorm (mollify k (g a) - g a) 2 (potentialMeasure φ))
    atTop (𝓝 0)
  exact eLpNorm_compact_mollify_sub_potential_tendsto_zero hφ (hg a) (hgc a)

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.eLpNorm_continuous_mul_compact_mollify_sub_potential_tendsto_zero
#print axioms KLS.DeterministicBridgeIntegration.HasWeakMatrixDerivative.compact_smoothing

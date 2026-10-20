import KLSConstantImprovement.ActualSourceHessianCutoffSubsequence405
import KLSConstantImprovement.ActualSourceHessianLimitIdentification405

/-! Strong local L2 convergence of the actual source Hessians, on one
subsequence and to the actual Hessian of the limiting C1,1 source.  The
local compactness is paid by the actual third tensor curvature budget. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ContDiff ENNReal
namespace KLSConstantImprovement.ActualSourceHessianStrongLimit405
open KLS ActualBoundedCanonicalSource ActualSourceHessianCutoffSubsequence405
open ActualSourceHessianLimitIdentification405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {ρ : ℕ → Measure (Space n)} {μ : Measure (Space n)}

theorem local_eLpNorm_tendsto_of_source_cutoffs
    {f : ℕ → Space n → ℝ} {g : Space n → ℝ}
    (ht : ∀ m, Tendsto (fun k => eLpNorm
      (fun x => hessianSourceCutoff n m x*f k x-hessianSourceCutoff n m x*g x)
      2 volume) atTop (𝓝 0))
    (E : Set (Space n)) (hE : IsCompact E) :
    Tendsto (fun k => eLpNorm (fun x => f k x-g x) 2 (volume.restrict E)) atTop (𝓝 0) := by
  obtain ⟨R, _hR, hR⟩ := hE.isBounded.exists_pos_norm_le
  obtain ⟨m, hm⟩ := exists_nat_ge R
  have hχE (x : Space n) (hx : x ∈ E) : hessianSourceCutoff n m x = 1 := by
    apply hessianSourceCutoff_one
    simp only [mem_closedBall, dist_zero_right]
    exact (hR x hx).trans (by linarith)
  have hb (k : ℕ) : eLpNorm (fun x => f k x-g x) 2 (volume.restrict E) ≤
      eLpNorm (fun x => hessianSourceCutoff n m x*f k x-hessianSourceCutoff n m x*g x)
        2 volume := by
    calc
      _ = eLpNorm (fun x => hessianSourceCutoff n m x*f k x-hessianSourceCutoff n m x*g x)
          2 (volume.restrict E) := by
        apply eLpNorm_congr_ae
        filter_upwards [ae_restrict_mem hE.measurableSet] with x hx
        simp only [hχE x hx, one_mul]
      _ ≤ _ := eLpNorm_mono_measure _ Measure.restrict_le_self
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (ht m) (fun _ => bot_le) hb

theorem exists_actual_hessian_strong_local_subsequence
    (d : ∀ k, SourceData (ρ k)) (e : SourceData μ)
    (hiso : ∀ k, IsIsotropic (ρ k))
    {c : ℝ} (hc : 0 < c) (hκ : ∀ k, c ≤ (d k).targetConvexityConstant)
    (hgrad0 : ∀ k, gradient (d k).potential 0 = 0)
    {z : ℝ} (hlim0 : Tendsto (fun k => (d k).potential (0 : Space n)) atTop (𝓝 z))
    (hgradlim : ∀ x, Tendsto (fun k => gradient (d k).potential x) atTop
      (𝓝 (gradient e.potential x))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∀ m a b, Tendsto (fun k => eLpNorm
        (fun x => hessianSourceCutoff n m x*coordinateHessian (d (σ k)).potential x a b-
          hessianSourceCutoff n m x*coordinateHessian e.potential x a b) 2 volume)
        atTop (𝓝 0)) ∧
      (∀ (E : Set (Space n)), IsCompact E → ∀ a b, Tendsto (fun k => eLpNorm
        (fun x => coordinateHessian (d (σ k)).potential x a b-
          coordinateHessian e.potential x a b) 2 (volume.restrict E)) atTop (𝓝 0)) := by
  obtain ⟨g, σ, hσ, ht⟩ :=
    exists_actual_hessian_cutoff_strong_subsequence d hiso hc hκ hgrad0 hlim0
  let L : ℝ≥0 := ⟨16/c, div_nonneg (by norm_num) hc.le⟩
  have hL (k : ℕ) : LipschitzWith L (gradient (d k).potential) := by
    apply (d k).gradient_lipschitz.weaken
    change 16/(d k).targetConvexityConstant ≤ 16/c
    exact div_le_div_of_nonneg_left (by norm_num) hc (hκ k)
  have hg (m : ℕ) (a b : Fin n) :
      (g m a b : Space n → ℝ) =ᵐ[volume]
        (fun x => hessianSourceCutoff n m x*coordinateHessian e.potential x a b) :=
    actual_hessian_cutoff_limit_identified (fun k => d (σ k)) e
      (fun k => hL (σ k)) (fun k => hgrad0 (σ k))
      (fun x => (hgradlim x).comp hσ.tendsto_atTop)
      (hessianSourceCutoff n m).contDiff (hessianSourceCutoff n m).hasCompactSupport
      a b (g m a b) (ht m a b)
  have hcut (m : ℕ) (a b : Fin n) : Tendsto (fun k => eLpNorm
      (fun x => hessianSourceCutoff n m x*coordinateHessian (d (σ k)).potential x a b-
        hessianSourceCutoff n m x*coordinateHessian e.potential x a b) 2 volume)
      atTop (𝓝 0) := by
    convert ht m a b using 1
    funext k
    exact (eLpNorm_congr_ae (EventuallyEq.rfl.sub (hg m a b))).symm
  refine ⟨σ, hσ, hcut, fun E hE a b => ?_⟩
  exact local_eLpNorm_tendsto_of_source_cutoffs (fun m => hcut m a b) E hE

end KLSConstantImprovement.ActualSourceHessianStrongLimit405
#print axioms KLSConstantImprovement.ActualSourceHessianStrongLimit405.local_eLpNorm_tendsto_of_source_cutoffs
#print axioms KLSConstantImprovement.ActualSourceHessianStrongLimit405.exists_actual_hessian_strong_local_subsequence

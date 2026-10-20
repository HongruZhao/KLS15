import KLSConstantImprovement.ActualSourceHessianStrongLimit405
import KLSConstantImprovement.ActualCountableLpAesubsequence405

/-! The genuine local source-Hessian compactness yields one common
subsequence with strong local L2 and almost-everywhere matrix convergence
to the actual Hessian of the limiting source. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ContDiff ENNReal
namespace KLSConstantImprovement.ActualSourceHessianAELimit405
open KLS ActualBoundedCanonicalSource ActualSourceHessianCutoffSubsequence405
open ActualSourceHessianLimitIdentification405 ActualSourceHessianStrongLimit405
open ActualCountableLpAesubsequence405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {ρ : ℕ → Measure (Space n)} {μ : Measure (Space n)}

theorem actual_hessian_ae_subsequence_of_cutoff_strong
    (d : ∀ k, SourceData (ρ k)) (e : SourceData μ)
    (hcut : ∀ m a b, Tendsto (fun k => eLpNorm
      (fun x => hessianSourceCutoff n m x*coordinateHessian (d k).potential x a b-
        hessianSourceCutoff n m x*coordinateHessian e.potential x a b) 2 volume)
      atTop (𝓝 0)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ᵐ x ∂(volume : Measure (Space n)),
      Tendsto (fun k => coordinateHessian (d (σ k)).potential x) atTop
        (𝓝 (coordinateHessian e.potential x)) := by
  have hf (k : ℕ) (i : ℕ × Fin n × Fin n) :=
    actual_hessian_compact_multiplier_memLp (d k)
      (hessianSourceCutoff n i.1).contDiff (hessianSourceCutoff n i.1).hasCompactSupport
      i.2.1 i.2.2
  have hg (i : ℕ × Fin n × Fin n) :=
    actual_hessian_compact_multiplier_memLp e
      (hessianSourceCutoff n i.1).contDiff (hessianSourceCutoff n i.1).hasCompactSupport
      i.2.1 i.2.2
  let F (k : ℕ) (i : ℕ × Fin n × Fin n) : Lp ℝ 2 (volume : Measure (Space n)) :=
    (hf k i).toLp
      (fun x => hessianSourceCutoff n i.1 x*coordinateHessian (d k).potential x i.2.1 i.2.2)
  let G (i : ℕ × Fin n × Fin n) : Lp ℝ 2 (volume : Measure (Space n)) :=
    (hg i).toLp
      (fun x => hessianSourceCutoff n i.1 x*coordinateHessian e.potential x i.2.1 i.2.2)
  have ht (i : ℕ × Fin n × Fin n) : Tendsto (fun k => F k i) atTop (𝓝 (G i)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun k x => hessianSourceCutoff n i.1 x*coordinateHessian (d k).potential x i.2.1 i.2.2)
      (fun k => hf k i)
      (fun x => hessianSourceCutoff n i.1 x*coordinateHessian e.potential x i.2.1 i.2.2)
      (hg i)).mpr (hcut i.1 i.2.1 i.2.2)
  obtain ⟨σ, hσ, hae⟩ := exists_countable_Lp_common_ae_subsequence F G ht
  have hFr : ∀ᵐ x ∂(volume : Measure (Space n)), ∀ (i : ℕ × Fin n × Fin n) k,
      F k i x = hessianSourceCutoff n i.1 x*coordinateHessian (d k).potential x i.2.1 i.2.2 :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun k => (hf k i).coeFn_toLp
  have hGr : ∀ᵐ x ∂(volume : Measure (Space n)), ∀ i : ℕ × Fin n × Fin n,
      G i x = hessianSourceCutoff n i.1 x*coordinateHessian e.potential x i.2.1 i.2.2 :=
    ae_all_iff.mpr fun i => (hg i).coeFn_toLp
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [hae, hFr, hGr] with x hx hfx hgx
  obtain ⟨m, hm⟩ := exists_nat_ge ‖x‖
  have hχ : hessianSourceCutoff n m x = 1 := by
    apply hessianSourceCutoff_one
    simp only [mem_closedBall, dist_zero_right]
    linarith
  apply tendsto_pi_nhds.mpr
  intro a
  apply tendsto_pi_nhds.mpr
  intro b
  have htt := hx (m,a,b)
  rw [hgx (m,a,b)] at htt
  have htt' : Tendsto
      (fun k => hessianSourceCutoff n m x*coordinateHessian (d (σ k)).potential x a b)
      atTop (𝓝 (hessianSourceCutoff n m x*coordinateHessian e.potential x a b)) :=
    htt.congr' (Eventually.of_forall fun k => hfx (m,a,b) (σ k))
  simpa only [hχ, one_mul] using htt'

theorem exists_actual_hessian_strong_local_ae_subsequence
    (d : ∀ k, SourceData (ρ k)) (e : SourceData μ)
    (hiso : ∀ k, IsIsotropic (ρ k))
    {c : ℝ} (hc : 0 < c) (hκ : ∀ k, c ≤ (d k).targetConvexityConstant)
    (hgrad0 : ∀ k, gradient (d k).potential 0 = 0)
    {z : ℝ} (hlim0 : Tendsto (fun k => (d k).potential (0 : Space n)) atTop (𝓝 z))
    (hgradlim : ∀ x, Tendsto (fun k => gradient (d k).potential x) atTop
      (𝓝 (gradient e.potential x))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∀ (E : Set (Space n)), IsCompact E → ∀ a b, Tendsto (fun k => eLpNorm
        (fun x => coordinateHessian (d (σ k)).potential x a b-
          coordinateHessian e.potential x a b) 2 (volume.restrict E)) atTop (𝓝 0)) ∧
      (∀ᵐ x ∂(volume : Measure (Space n)),
        Tendsto (fun k => coordinateHessian (d (σ k)).potential x) atTop
          (𝓝 (coordinateHessian e.potential x))) := by
  obtain ⟨s, hs, hcut, hlocal⟩ := exists_actual_hessian_strong_local_subsequence
    d e hiso hc hκ hgrad0 hlim0 hgradlim
  obtain ⟨t, ht, hae⟩ :=
    actual_hessian_ae_subsequence_of_cutoff_strong (fun k => d (s k)) e hcut
  exact ⟨fun k => s (t k), hs.comp ht,
    (fun E hE a b => (hlocal E hE a b).comp ht.tendsto_atTop), hae⟩

end KLSConstantImprovement.ActualSourceHessianAELimit405
#print axioms KLSConstantImprovement.ActualSourceHessianAELimit405.actual_hessian_ae_subsequence_of_cutoff_strong
#print axioms KLSConstantImprovement.ActualSourceHessianAELimit405.exists_actual_hessian_strong_local_ae_subsequence

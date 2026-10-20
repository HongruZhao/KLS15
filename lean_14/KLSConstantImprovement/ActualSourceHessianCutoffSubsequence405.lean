import KLSConstantImprovement.ActualSourceHessianLocalPrecompact405
import KLSConstantImprovement.ActualCountableStrongSubsequence405

/-! One common strong-L2 subsequence for all actual Hessian entries on a
countable source exhaustion.  The cutoff values and weak derivatives were
paid before applying product compactness. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ContDiff ENNReal
namespace KLSConstantImprovement.ActualSourceHessianCutoffSubsequence405
open KLS ActualBoundedCanonicalSource ActualSourceHessianLocalPrecompact405
open ActualCountableStrongSubsequence405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {ρ : ℕ → Measure (Space n)}

def hessianSourceCutoff (n m : ℕ) : ContDiffBump (0 : Space n) :=
  ⟨(m : ℝ)+1, (m : ℝ)+2, by positivity, by linarith⟩

theorem hessianSourceCutoff_one (m : ℕ) {x : Space n}
    (hx : x ∈ closedBall (0 : Space n) ((m : ℝ)+1)) : hessianSourceCutoff n m x = 1 :=
  (hessianSourceCutoff n m).one_of_mem_closedBall hx

theorem exists_actual_hessian_cutoff_strong_subsequence
    (d : ∀ k, SourceData (ρ k)) (hiso : ∀ k, IsIsotropic (ρ k))
    {c : ℝ} (hc : 0 < c) (hκ : ∀ k, c ≤ (d k).targetConvexityConstant)
    (hgrad0 : ∀ k, gradient (d k).potential 0 = 0)
    {z : ℝ} (hlim0 : Tendsto (fun k => (d k).potential (0 : Space n)) atTop (𝓝 z)) :
    ∃ (g : ℕ → Fin n → Fin n → Lp ℝ 2 (volume : Measure (Space n))) (σ : ℕ → ℕ),
      StrictMono σ ∧ ∀ m a b,
        Tendsto (fun k => eLpNorm
          (fun x => hessianSourceCutoff n m x * coordinateHessian (d (σ k)).potential x a b - g m a b x)
          2 volume) atTop (𝓝 0) := by
  have hχ (m : ℕ) : ContDiff ℝ 1 (hessianSourceCutoff n m) :=
    (hessianSourceCutoff n m).contDiff
  choose hf htb using fun m a b => actual_hessian_cutoff_precompact d hiso hc hκ hgrad0 hlim0
    (hχ m)
    (hessianSourceCutoff n m).hasCompactSupport a b
  let F : ℕ → (ℕ × Fin n × Fin n) → Lp ℝ 2 (volume : Measure (Space n)) := fun k i =>
    (hf i.1 i.2.1 i.2.2 k).toLp
      (fun x => hessianSourceCutoff n i.1 x * coordinateHessian (d k).potential x i.2.1 i.2.2)
  have hF (i : ℕ × Fin n × Fin n) : TotallyBounded (range (fun k => F k i)) :=
    htb i.1 i.2.1 i.2.2
  obtain ⟨g, σ, hσ, ht⟩ := exists_common_strong_subsequence F hF
  refine ⟨fun m a b => g (m,a,b), σ, hσ, fun m a b => ?_⟩
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun k x => hessianSourceCutoff n m x * coordinateHessian (d (σ k)).potential x a b)
    (fun k => hf m a b (σ k)) (g (m,a,b)) (Lp.memLp _)).mp
  simpa only [F, Lp.toLp_coeFn] using ht (m,a,b)

end KLSConstantImprovement.ActualSourceHessianCutoffSubsequence405
#print axioms KLSConstantImprovement.ActualSourceHessianCutoffSubsequence405.hessianSourceCutoff_one
#print axioms KLSConstantImprovement.ActualSourceHessianCutoffSubsequence405.exists_actual_hessian_cutoff_strong_subsequence

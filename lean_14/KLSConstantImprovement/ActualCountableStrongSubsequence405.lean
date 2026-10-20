import KLSConstantImprovement.ActualCompactRawH1Precompact405
import Mathlib.Topology.Sequences
import Mathlib.Topology.Compactness.Compact

/-! One common strong subsequence for countably many genuinely precompact
Hilbert coordinates.  This is countable product compactness, not a separate
unrelated subsequence for each Hessian entry or source ball. -/
noncomputable section
open Set Filter
open scoped Topology
namespace KLSConstantImprovement.ActualCountableStrongSubsequence405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

theorem exists_common_strong_subsequence
    {ι E : Type*} [Countable ι] [MetricSpace E] [CompleteSpace E]
    (F : ℕ → ι → E) (hF : ∀ i, TotallyBounded (range (fun k => F k i))) :
    ∃ (g : ι → E) (σ : ℕ → ℕ), StrictMono σ ∧
      ∀ i, Tendsto (fun k => F (σ k) i) atTop (𝓝 (g i)) := by
  have hK : IsCompact (Set.pi univ (fun i => closure (range (fun k => F k i)))) :=
    isCompact_univ_pi fun i => (hF i).closure.isCompact_of_isClosed isClosed_closure
  have hm (k : ℕ) : F k ∈ Set.pi univ (fun i => closure (range (fun k => F k i))) := by
    intro i _
    exact subset_closure (mem_range_self k)
  obtain ⟨g, _, σ, hσ, ht⟩ := hK.tendsto_subseq hm
  refine ⟨g, σ, hσ, fun i => ?_⟩
  simpa only [Function.comp_def] using (continuous_apply i).continuousAt.tendsto.comp ht

end KLSConstantImprovement.ActualCountableStrongSubsequence405
#print axioms KLSConstantImprovement.ActualCountableStrongSubsequence405.exists_common_strong_subsequence

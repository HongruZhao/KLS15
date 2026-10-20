import KLSConstantImprovement.ActualBoundedSourceCalculus
import KLS.WeightedFaithfulCutoff

/-! On the final original bounded target source, sufficiently large target
cutoffs are identically one everywhere on the source.  Thus removal of
target cutoffs at the final endpoint needs no source-tail energy estimate. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace KLSConstantImprovement.ActualTargetCutoffPlateau405
open KLS ActualBoundedCanonicalSource
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_target_pullback_cutoffs_eventually_one (d : SourceData μ) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ x : Space n,
      smoothCutoff n m (gradient d.potential x) = 1 := by
  obtain ⟨R, _hR, hR⟩ := d.gradient_range_bounded.exists_pos_norm_le
  obtain ⟨N, hN⟩ := exists_nat_ge R
  refine ⟨N, fun m hm x => ?_⟩
  apply smoothCutoff_eq_one_of_norm_le
  have hb := hR (gradient d.potential x) (mem_range_self x)
  have hNm : (N : ℝ) ≤ m := by exact_mod_cast hm
  linarith

end KLSConstantImprovement.ActualTargetCutoffPlateau405
#print axioms KLSConstantImprovement.ActualTargetCutoffPlateau405.actual_target_pullback_cutoffs_eventually_one

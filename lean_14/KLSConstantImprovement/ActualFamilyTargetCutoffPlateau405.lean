import KLSConstantImprovement.ActualTargetCutoffPlateau405
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-! Fixed compact source masks lie in the plateau of every sufficiently
large target cutoff, eventually along the actual converging source family.
Only uniform gradient convergence on that compact mask and the genuine
bounded gradient range of the final source are used. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ContDiff
namespace KLSConstantImprovement.ActualFamilyTargetCutoffPlateau405
open KLS ActualBoundedCanonicalSource
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {ρ : ℕ → Measure (Space n)} {μ : Measure (Space n)}

theorem actual_family_target_cutoff_plateau_on_compact
    (d : ∀ k, SourceData (ρ k)) (e : SourceData μ)
    (hg : TendstoLocallyUniformly (fun k => gradient (d k).potential)
      (gradient e.potential) atTop)
    (E : Set (Space n)) (hE : IsCompact E) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ᶠ k in atTop, ∀ x ∈ E,
      smoothCutoff n m (gradient (d k).potential x) = 1 := by
  obtain ⟨R, _hR, hR⟩ := e.gradient_range_bounded.exists_pos_norm_le
  obtain ⟨N, hN⟩ := exists_nat_ge R
  have hu : TendstoUniformlyOn (fun k => gradient (d k).potential)
      (gradient e.potential) atTop E :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hE).mp
      (hg.tendstoLocallyUniformlyOn.mono (subset_univ E))
  have hev : ∀ᶠ k in atTop, ∀ x ∈ E,
      dist (gradient e.potential x) (gradient (d k).potential x) < (1 : ℝ) :=
    Metric.tendstoUniformlyOn_iff.mp hu 1 one_pos
  refine ⟨N, fun m hm => hev.mono fun k hk x hx => ?_⟩
  apply smoothCutoff_eq_one_of_norm_le
  have hNm : (N : ℝ) ≤ m := by exact_mod_cast hm
  have hb := hR (gradient e.potential x) (mem_range_self x)
  have ht := dist_triangle (gradient (d k).potential x) (gradient e.potential x) (0 : Space n)
  simp only [dist_zero_right] at ht
  rw [dist_comm (gradient (d k).potential x) (gradient e.potential x)] at ht
  linarith [hk x hx]

end KLSConstantImprovement.ActualFamilyTargetCutoffPlateau405
#print axioms KLSConstantImprovement.ActualFamilyTargetCutoffPlateau405.actual_family_target_cutoff_plateau_on_compact

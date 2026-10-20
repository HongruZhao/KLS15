import KLS.SmoothCutoffSequence
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
A concrete smooth bounded value truncation. Its derivative has a single
uniform bound, and both the value and derivative eventually equal those
of the identity at every finite real input. These are actual functions,
not supplied approximation witnesses.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology NNReal
namespace KLSConstantImprovement.ActualSmoothScalarTruncation405
open KLS

def scalarBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

def scalarSeed (t : ℝ) : ℝ := t * scalarBump t

def scalarClip (k : ℕ) (t : ℝ) : ℝ := t * scalarBump (cutoffScale k * t)

theorem scalarSeed_contDiff : ContDiff ℝ 3 scalarSeed :=
  contDiff_id.mul scalarBump.contDiff

theorem scalarSeed_compact : HasCompactSupport scalarSeed :=
  scalarBump.hasCompactSupport.of_isClosed_subset (isClosed_tsupport scalarSeed)
    tsupport_mul_subset_right

theorem scalarClip_contDiff (k : ℕ) : ContDiff ℝ 3 (scalarClip k) :=
  contDiff_id.mul (scalarBump.contDiff.comp (contDiff_const.mul contDiff_id))

theorem scalarClip_compact (k : ℕ) : HasCompactSupport (scalarClip k) :=
  (scalarBump.hasCompactSupport.comp_smul (cutoffScale_pos k).ne').of_isClosed_subset
    (isClosed_tsupport (scalarClip k)) tsupport_mul_subset_right

theorem scalarClip_zero (k : ℕ) : scalarClip k 0 = 0 := by simp [scalarClip]

theorem scalarClip_norm_le (k : ℕ) (t : ℝ) : ‖scalarClip k t‖ ≤ ‖t‖ := by
  change ‖t * scalarBump (cutoffScale k * t)‖ ≤ ‖t‖
  rw [norm_mul, Real.norm_of_nonneg scalarBump.nonneg]
  exact mul_le_of_le_one_right (norm_nonneg t) scalarBump.le_one

theorem scalarClip_deriv (k : ℕ) (t : ℝ) :
    deriv (scalarClip k) t = deriv scalarSeed (cutoffScale k * t) := by
  have hb (s : ℝ) : HasDerivAt (scalarBump : ℝ → ℝ) (deriv scalarBump s) s :=
    (scalarBump.contDiff : ContDiff ℝ 1 (scalarBump : ℝ → ℝ)).differentiable one_ne_zero s
      |>.hasDerivAt
  have hs := ((hasDerivAt_id (cutoffScale k * t)).mul (hb (cutoffScale k * t))).deriv
  have hk := ((hasDerivAt_id t).mul
    ((hb (cutoffScale k * t)).comp t ((hasDerivAt_id t).const_mul (cutoffScale k)))).deriv
  change deriv scalarSeed (cutoffScale k * t) =
    1 * scalarBump (cutoffScale k * t) +
      (cutoffScale k * t) * deriv scalarBump (cutoffScale k * t) at hs
  change deriv (scalarClip k) t =
    1 * scalarBump (cutoffScale k * t) +
      t * (deriv scalarBump (cutoffScale k * t) * (cutoffScale k * 1)) at hk
  rw [hk, hs]
  ring

theorem scalarClip_lipschitz (k : ℕ) :
    ∃ L D : ℝ≥0, LipschitzWith L (scalarClip k) ∧ LipschitzWith D (deriv (scalarClip k)) := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (scalarClip_compact k) (scalarClip_contDiff k) (by norm_num)
  have hc : ContDiff ℝ 2 (deriv (scalarClip k)) :=
    (show ContDiff ℝ (2 + 1) (scalarClip k) from scalarClip_contDiff k).deriv'
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (scalarClip_compact k).deriv hc (by norm_num)
  exact ⟨L, D, hL, hD⟩

theorem scalarClip_uniform_deriv_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k t, ‖deriv (scalarClip k) t‖ ≤ B := by
  have hc : Continuous (deriv scalarSeed) :=
    (scalarSeed_contDiff.of_le (by norm_num) : ContDiff ℝ 1 scalarSeed).continuous_deriv_one
  obtain ⟨B, hB⟩ := scalarSeed_compact.deriv.exists_bound_of_continuous hc
  exact ⟨B, (norm_nonneg _).trans (hB 0), fun k t => by rw [scalarClip_deriv]; exact hB _⟩

theorem scalarSeed_deriv_eq_one {t : ℝ} (ht : ‖t‖ < 1) : deriv scalarSeed t = 1 := by
  have he : scalarSeed =ᶠ[𝓝 t] (fun s : ℝ => s) := by
    have hb := scalarBump.eventuallyEq_one_of_mem_ball
      (show t ∈ Metric.ball (0 : ℝ) scalarBump.rIn from by
        simpa only [scalarBump, Metric.mem_ball, dist_zero_right] using ht)
    filter_upwards [hb] with s hs
    change s * scalarBump s = s
    simp only [hs, Pi.one_apply, mul_one]
  simpa only [deriv_id''] using he.deriv_eq

theorem scalarClip_eventually_identity (t : ℝ) :
    ∀ᶠ k in atTop, scalarClip k t = t ∧ deriv (scalarClip k) t = 1 := by
  have ht : Tendsto (fun k => cutoffScale k * t) atTop (𝓝 (0 : ℝ)) := by
    simpa using cutoffScale_tendsto_zero.mul_const t
  filter_upwards [ht.eventually (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)] with k hk
  have hn : ‖cutoffScale k * t‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hk
  constructor
  · change t * scalarBump (cutoffScale k * t) = t
    rw [scalarBump.one_of_mem_closedBall
      (show cutoffScale k * t ∈ Metric.closedBall (0 : ℝ) scalarBump.rIn from by
        simpa only [scalarBump, Metric.mem_closedBall, dist_zero_right] using hn.le), mul_one]
  · rw [scalarClip_deriv]
    exact scalarSeed_deriv_eq_one hn

end KLSConstantImprovement.ActualSmoothScalarTruncation405

#print axioms KLSConstantImprovement.ActualSmoothScalarTruncation405.scalarClip_contDiff
#print axioms KLSConstantImprovement.ActualSmoothScalarTruncation405.scalarClip_compact
#print axioms KLSConstantImprovement.ActualSmoothScalarTruncation405.scalarClip_norm_le
#print axioms KLSConstantImprovement.ActualSmoothScalarTruncation405.scalarClip_deriv
#print axioms KLSConstantImprovement.ActualSmoothScalarTruncation405.scalarClip_lipschitz
#print axioms KLSConstantImprovement.ActualSmoothScalarTruncation405.scalarClip_uniform_deriv_bound
#print axioms KLSConstantImprovement.ActualSmoothScalarTruncation405.scalarClip_eventually_identity

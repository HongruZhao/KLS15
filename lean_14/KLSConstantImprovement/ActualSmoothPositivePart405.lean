import KLSConstantImprovement.ActualSmoothKatoRegularizer405
import KLS.SmoothCutoffSequence
import Mathlib.Analysis.Calculus.MeanValue

/-! C1 Lipschitz approximants to the positive part, including the exact
limiting slope 1/2 at zero.  This convention gives a genuine weak derivative
without first assuming a level-set gradient-vanishing theorem. -/
noncomputable section
open Filter
open scoped Topology ContDiff NNReal
namespace KLSConstantImprovement.ActualSmoothPositivePart405
open KLS ActualSmoothKatoRegularizer405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

def smoothPositivePart (ε t : ℝ) : ℝ := (t+katoRho ε t)/2
def smoothPositivePartSlope (ε t : ℝ) : ℝ := (1+t/katoRho ε t)/2
def positivePartSlope (t : ℝ) : ℝ := if 0 < t then 1 else if t < 0 then 0 else 1/2

theorem smoothPositivePart_contDiff {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 1 (smoothPositivePart ε) := by
  have hr : ContDiff ℝ 1 (katoRho ε) :=
    ((contDiff_id.pow 2).add contDiff_const).sqrt (fun t => by nlinarith [sq_nonneg t])
  exact (contDiff_id.add hr).div_const 2

theorem smoothPositivePart_hasDerivAt {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (smoothPositivePart ε) (smoothPositivePartSlope ε t) t := by
  have hs : HasDerivAt (fun y : ℝ => y+katoRho ε y) (1+t/katoRho ε t) t :=
    (hasDerivAt_id t).add (katoRho_hasDerivAt hε t)
  have hh := (hasDerivAt_mul_const (x := t+katoRho ε t) (1/2 : ℝ)).comp t hs
  have hefun : (fun y : ℝ => (y+katoRho ε y)*(1/2 : ℝ)) = smoothPositivePart ε := by
    funext y
    dsimp only [smoothPositivePart]
    ring
  dsimp only [Function.comp_def] at hh
  rw [hefun] at hh
  apply hh.congr_deriv
  dsimp only [smoothPositivePartSlope]
  ring

theorem smoothPositivePartSlope_bounds {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    0 ≤ smoothPositivePartSlope ε t ∧ smoothPositivePartSlope ε t ≤ 1 := by
  have hr := katoRho_positive hε t
  have hab : |t| ≤ katoRho ε t := by
    apply Real.le_sqrt_of_sq_le
    simpa only [sq_abs] using
      (le_add_of_nonneg_right (sq_nonneg ε) : t^2 ≤ t^2+ε^2)
  have hlo : -katoRho ε t ≤ t := (abs_le.mp hab).1
  have hhi : t ≤ katoRho ε t := (abs_le.mp hab).2
  have h0 : -1 ≤ t/katoRho ε t := (le_div_iff₀ hr).mpr (by linarith)
  have h1 : t/katoRho ε t ≤ 1 := (div_le_iff₀ hr).mpr (by linarith)
  dsimp only [smoothPositivePartSlope]
  constructor <;> linarith

theorem smoothPositivePart_lipschitz {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith 1 (smoothPositivePart ε) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t => (smoothPositivePart_hasDerivAt hε t).differentiableAt)
  intro t
  change ‖deriv (smoothPositivePart ε) t‖ ≤ (1 : ℝ)
  rw [(smoothPositivePart_hasDerivAt hε t).deriv, Real.norm_eq_abs,
    abs_of_nonneg (smoothPositivePartSlope_bounds hε t).1]
  exact (smoothPositivePartSlope_bounds hε t).2

theorem smoothPositivePart_value_bounds {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (t : ℝ) :
    0 ≤ smoothPositivePart ε t ∧ smoothPositivePart ε t ≤ |t|+1 := by
  have hr := katoRho_positive hε t
  have hr2 := katoRho_square (ε := ε) (t := t)
  have hab : |t| ≤ katoRho ε t := by
    apply Real.le_sqrt_of_sq_le
    simpa only [sq_abs] using
      (le_add_of_nonneg_right (sq_nonneg ε) : t^2 ≤ t^2+ε^2)
  have hlo := (abs_le.mp hab).1
  have hupper : katoRho ε t ≤ |t|+ε := by
    nlinarith [sq_abs t, abs_nonneg t, mul_nonneg (abs_nonneg t) hε.le]
  dsimp only [smoothPositivePart]
  constructor
  · linarith
  · have ht := le_abs_self t
    linarith

theorem katoRho_cutoffScale_tendsto (t : ℝ) :
    Tendsto (fun k => katoRho (cutoffScale k) t) atTop (𝓝 |t|) := by
  have ht : Tendsto (fun k => t^2+(cutoffScale k)^2) atTop (𝓝 (t^2)) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using
      (tendsto_const_nhds.add (cutoffScale_tendsto_zero.pow 2))
  simpa only [katoRho, Real.sqrt_sq_eq_abs, Function.comp_def] using
    (Real.continuous_sqrt.tendsto (t^2)).comp ht

theorem smoothPositivePart_cutoffScale_tendsto (t : ℝ) :
    Tendsto (fun k => smoothPositivePart (cutoffScale k) t) atTop (𝓝 (max t 0)) := by
  have he : (t+|t|)/2 = max t 0 := by
    by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg ht, max_eq_left ht]
      ring
    · rw [abs_of_neg (lt_of_not_ge ht), max_eq_right (le_of_not_ge ht)]
      ring
  have hh : Tendsto (fun k => (t+katoRho (cutoffScale k) t)/2) atTop (𝓝 ((t+|t|)/2)) :=
    (tendsto_const_nhds.add (katoRho_cutoffScale_tendsto t)).div_const 2
  simpa only [smoothPositivePart, he] using hh

theorem smoothPositivePartSlope_cutoffScale_tendsto (t : ℝ) :
    Tendsto (fun k => smoothPositivePartSlope (cutoffScale k) t) atTop (𝓝 (positivePartSlope t)) := by
  by_cases ht : t = 0
  · subst t
    simpa only [smoothPositivePartSlope, positivePartSlope, lt_self_iff_false, if_false,
      zero_div, add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1/2 : ℝ)) atTop (𝓝 (1/2)))
  · have hh : Tendsto (fun k => (1+t/katoRho (cutoffScale k) t)/2) atTop
        (𝓝 ((1+t/|t|)/2)) :=
      (tendsto_const_nhds.add
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => t) atTop (𝓝 t)).div
          (katoRho_cutoffScale_tendsto t) (abs_ne_zero.mpr ht))).div_const 2
    have he : (1+t/|t|)/2 = positivePartSlope t := by
      rcases lt_or_gt_of_ne ht with hn | hp
      · rw [positivePartSlope, if_neg (not_lt.mpr hn.le), if_pos hn, abs_of_neg hn]
        field_simp [ht]
        ring
      · rw [positivePartSlope, if_pos hp, abs_of_pos hp, div_self ht]
        norm_num
    simpa only [smoothPositivePartSlope, he] using hh

theorem positivePartSlope_bounds (t : ℝ) :
    0 ≤ positivePartSlope t ∧ positivePartSlope t ≤ 1 := by
  dsimp only [positivePartSlope]
  split_ifs <;> norm_num

theorem positivePartSlope_mul_positivePart (t : ℝ) :
    max t 0*positivePartSlope t = max t 0 := by
  by_cases ht : 0 < t
  · rw [positivePartSlope, if_pos ht, mul_one]
  · rw [max_eq_right (not_lt.mp ht), zero_mul]

end KLSConstantImprovement.ActualSmoothPositivePart405
#print axioms KLSConstantImprovement.ActualSmoothPositivePart405.smoothPositivePart_contDiff
#print axioms KLSConstantImprovement.ActualSmoothPositivePart405.smoothPositivePart_hasDerivAt
#print axioms KLSConstantImprovement.ActualSmoothPositivePart405.smoothPositivePartSlope_bounds
#print axioms KLSConstantImprovement.ActualSmoothPositivePart405.smoothPositivePart_lipschitz
#print axioms KLSConstantImprovement.ActualSmoothPositivePart405.smoothPositivePart_value_bounds
#print axioms KLSConstantImprovement.ActualSmoothPositivePart405.katoRho_cutoffScale_tendsto
#print axioms KLSConstantImprovement.ActualSmoothPositivePart405.smoothPositivePart_cutoffScale_tendsto
#print axioms KLSConstantImprovement.ActualSmoothPositivePart405.smoothPositivePartSlope_cutoffScale_tendsto
#print axioms KLSConstantImprovement.ActualSmoothPositivePart405.positivePartSlope_bounds
#print axioms KLSConstantImprovement.ActualSmoothPositivePart405.positivePartSlope_mul_positivePart

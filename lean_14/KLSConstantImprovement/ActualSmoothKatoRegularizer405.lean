import KLSConstantImprovement.ActualCovariantKatoAlgebra405
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! A globally smooth square-root regularizer for nonnegative natural
mass. Its exact curvature coefficient remains nonnegative after Kato
absorption. This finite calculus does not assert admissibility of any
nonlinear weak PDE test. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace KLSConstantImprovement.ActualSmoothKatoRegularizer405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def katoRho (ε t : ℝ) : ℝ := Real.sqrt (t ^ 2 + ε ^ 2)
def katoRegularizer (ε t : ℝ) : ℝ := Real.sqrt (katoRho ε t)
def katoFirst (ε t : ℝ) : ℝ := t / (2 * katoRho ε t * katoRegularizer ε t)
def katoSecond (ε t : ℝ) : ℝ :=
  (2 * ε ^ 2 - t ^ 2) / (4 * katoRho ε t ^ 3 * katoRegularizer ε t)

theorem katoRho_positive {ε : ℝ} (hε : 0 < ε) (t : ℝ) : 0 < katoRho ε t :=
  Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])

theorem katoRegularizer_positive {ε : ℝ} (hε : 0 < ε) (t : ℝ) : 0 < katoRegularizer ε t :=
  Real.sqrt_pos.mpr (katoRho_positive hε t)

theorem katoRho_square {ε t : ℝ} : katoRho ε t ^ 2 = t ^ 2 + ε ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg t) (sq_nonneg ε))

theorem katoRegularizer_square {ε t : ℝ} : katoRegularizer ε t ^ 2 = katoRho ε t :=
  Real.sq_sqrt (Real.sqrt_nonneg _)

theorem katoRegularizer_contDiff {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 2 (katoRegularizer ε) := by
  have hr : ContDiff ℝ 2 (katoRho ε) :=
    ((contDiff_id.pow 2).add contDiff_const).sqrt (fun t => by nlinarith [sq_nonneg t])
  exact hr.sqrt (fun t => (katoRho_positive hε t).ne')

theorem katoRho_hasDerivAt {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (katoRho ε) (t / katoRho ε t) t := by
  have hr := (((hasDerivAt_id t).pow 2).add_const (ε ^ 2)).sqrt
    (by nlinarith [sq_nonneg t] : t ^ 2 + ε ^ 2 ≠ 0)
  have hfun : (fun y : ℝ => Real.sqrt ((id ^ 2) y + ε ^ 2)) = katoRho ε := by
    funext y
    simp only [Pi.pow_apply, id_eq, katoRho]
  rw [hfun] at hr
  apply hr.congr_deriv
  simp only [Pi.pow_apply, id_eq, Nat.reduceSub, pow_one, mul_one, katoRho]
  field_simp <;> ring

theorem katoRegularizer_hasDerivAt {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (katoRegularizer ε) (katoFirst ε t) t := by
  have hr := (katoRho_hasDerivAt hε t).sqrt (katoRho_positive hε t).ne'
  change HasDerivAt (katoRegularizer ε) ((t / katoRho ε t) / (2 * katoRegularizer ε t)) t at hr
  apply hr.congr_deriv
  unfold katoFirst
  field_simp <;> ring

theorem katoFirst_hasDerivAt {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (katoFirst ε) (katoSecond ε t) t := by
  have hr := katoRho_hasDerivAt hε t
  have hs := katoRegularizer_hasDerivAt hε t
  have hp := katoRho_positive hε t
  have hq := katoRegularizer_positive hε t
  have hd := (hr.const_mul 2).mul hs
  have ht := (hasDerivAt_id t).div hd (by positivity : 2 * katoRho ε t * katoRegularizer ε t ≠ 0)
  have hfun : (id / ((fun y : ℝ => 2 * katoRho ε y) * katoRegularizer ε)) = katoFirst ε := by
    funext y
    simp only [Pi.div_apply, Pi.mul_apply, id_eq, katoFirst]
  rw [hfun] at ht
  apply ht.congr_deriv
  simp only [Pi.mul_apply, id_eq, one_mul]
  dsimp only [katoSecond, katoFirst]
  have hr2 := katoRho_square (ε := ε) (t := t)
  have hs2 := katoRegularizer_square (ε := ε) (t := t)
  field_simp [hp.ne', hq.ne']
  nlinarith [sq_nonneg t, sq_nonneg ε,
    mul_nonneg hp.le (sq_nonneg t), mul_nonneg hp.le (sq_nonneg ε)]

theorem katoRegularizer_coefficient_bounds {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    0 ≤ katoFirst ε t ∧
      0 ≤ katoFirst ε t + 2 * t * katoSecond ε t ∧
      2 * katoFirst ε t * Real.sqrt t ≤ 1 ∧
      katoRegularizer ε t / 2 - Real.sqrt ε / 2 ≤ t * katoFirst ε t := by
  have hr := katoRho_positive hε t
  have hs := katoRegularizer_positive hε t
  have hr2 := katoRho_square (ε := ε) (t := t)
  have hs2 := katoRegularizer_square (ε := ε) (t := t)
  have htr : t ≤ katoRho ε t := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ε])
  have her : ε ≤ katoRho ε t := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg t])
  have hts : Real.sqrt t ≤ katoRegularizer ε t := Real.sqrt_le_sqrt htr
  have hes : Real.sqrt ε ≤ katoRegularizer ε t := Real.sqrt_le_sqrt her
  have hst : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  have hse : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
  have he2 := Real.sq_sqrt hε.le
  refine ⟨div_nonneg ht (by positivity), ?_, ?_, ?_⟩
  · have heq : katoFirst ε t + 2 * t * katoSecond ε t =
        (3 * t * ε ^ 2) / (2 * katoRho ε t ^ 3 * katoRegularizer ε t) := by
      dsimp only [katoFirst, katoSecond]
      field_simp [hr.ne', hs.ne']
      nlinarith [mul_nonneg ht (sq_nonneg ε)]
    rw [heq]
    positivity
  · have hmul : t * Real.sqrt t ≤ katoRho ε t * katoRegularizer ε t :=
      mul_le_mul htr hts hst hr.le
    have hform : 2 * katoFirst ε t * Real.sqrt t =
        (2 * t * Real.sqrt t) / (2 * katoRho ε t * katoRegularizer ε t) := by
      dsimp only [katoFirst]
      ring
    rw [hform]
    apply (div_le_iff₀ (by positivity : 0 < 2 * katoRho ε t * katoRegularizer ε t)).mpr
    nlinarith only [hmul]
  · have hmul : ε * Real.sqrt ε ≤ katoRho ε t * katoRegularizer ε t :=
      mul_le_mul her hes hse hr.le
    have heps : ε ^ 2 ≤ Real.sqrt ε * (katoRho ε t * katoRegularizer ε t) := by
      have hm := mul_le_mul_of_nonneg_left hmul hse
      nlinarith only [hm, he2]
    have heq : katoRegularizer ε t / 2 - t * katoFirst ε t =
        ε ^ 2 / (2 * katoRho ε t * katoRegularizer ε t) := by
      dsimp only [katoFirst]
      field_simp [hr.ne', hs.ne']
      nlinarith only [hr2, hs2]
    have heps' : ε ^ 2 / (2 * katoRho ε t * katoRegularizer ε t) ≤ Real.sqrt ε / 2 := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * katoRho ε t * katoRegularizer ε t)).mpr
      nlinarith only [heps]
    linarith

theorem katoRegularizer_chain_density_lower {ε M E P Γ D : ℝ}
    (hε : 0 < ε) (hM : 0 ≤ M) (hE : 0 ≤ E) (hP : 0 ≤ P) (hΓ : 0 ≤ Γ)
    (hD : 0 ≤ D) (hKato : D ≤ 4 * M * E) :
    katoRegularizer ε M / 2 - Real.sqrt ε / 2 ≤
      2 * katoFirst ε M * (E + (M + P) / 2 + Γ / 4) + katoSecond ε M * D := by
  obtain ⟨hf, hc, _hb, hm⟩ := katoRegularizer_coefficient_bounds hε hM
  have hP' : 0 ≤ katoFirst ε M * P := mul_nonneg hf hP
  have hΓ' : 0 ≤ katoFirst ε M * Γ := mul_nonneg hf hΓ
  by_cases hS : 0 ≤ katoSecond ε M
  · have hED := mul_nonneg hS hD
    have hEF := mul_nonneg hf hE
    nlinarith only [hm, hP', hΓ', hED, hEF]
  · have hd := mul_le_mul_of_nonpos_left hKato (le_of_lt (lt_of_not_ge hS))
    have he := mul_nonneg hc hE
    nlinarith only [hm, hP', hΓ', hd, he]

theorem katoRegularizer_tendsto {M : ℝ} (hM : 0 ≤ M) :
    Tendsto (fun k => katoRegularizer (KLS.cutoffScale k) M) atTop (𝓝 (Real.sqrt M)) := by
  have harg : Tendsto (fun k => M ^ 2 + KLS.cutoffScale k ^ 2) atTop (𝓝 (M ^ 2)) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using
      tendsto_const_nhds.add (KLS.cutoffScale_tendsto_zero.pow 2)
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp harg
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hroot
  change Tendsto (fun k => Real.sqrt (Real.sqrt (M ^ 2 + KLS.cutoffScale k ^ 2))) atTop
    (𝓝 (Real.sqrt (Real.sqrt (M ^ 2)))) at ht
  simpa only [katoRegularizer, katoRho, Real.sqrt_sq hM] using ht

end KLSConstantImprovement.ActualSmoothKatoRegularizer405
#print axioms KLSConstantImprovement.ActualSmoothKatoRegularizer405.katoRegularizer_hasDerivAt
#print axioms KLSConstantImprovement.ActualSmoothKatoRegularizer405.katoFirst_hasDerivAt
#print axioms KLSConstantImprovement.ActualSmoothKatoRegularizer405.katoRegularizer_coefficient_bounds
#print axioms KLSConstantImprovement.ActualSmoothKatoRegularizer405.katoRegularizer_chain_density_lower
#print axioms KLSConstantImprovement.ActualSmoothKatoRegularizer405.katoRegularizer_tendsto

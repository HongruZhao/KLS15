import KLS.MomentLegendreEnergy
import KLS.ConvexSectionNormalization
import KLS.WhitenedCutoffWeakLimit
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-! Actual dual-cap barriers for weak full-support source limits. These
lemmas construct uniform cones from bounded genuine Legendre energy and
compact continuous target test convergence. No full-support source or
inverse-mass estimate is assumed to follow without its remaining limits. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric InnerProductSpace
open scoped Topology BigOperators ENNReal NNReal
namespace KLSConstantImprovement.ActualDualCapCoercivity405
open KLS
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem dual_cap_barrier {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {φ β : Space n → ℝ} {K m a : ℝ}
    (hK : 0 ≤ K) (hm : 0 < m)
    (hE : momentDualEnergy μ φ ≤ ENNReal.ofReal K)
    (hβ : Integrable β μ) (hβ0 : ∀ p, 0 ≤ β p) (hβ1 : ∀ p, β p ≤ 1)
    (hβmass : m ≤ ∫ p, β p ∂μ) (x : Space n)
    (hcap : ∀ p, β p ≠ 0 → a * ‖x‖ ≤ inner ℝ p x) :
    a * ‖x‖ - K / m ≤ φ x := by
  have hfinite : momentDualEnergy μ φ ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hE
  have hI := integrable_normalizedLegendreTransform_toReal hfinite
  have hAE := ae_normalizedLegendreTransform_lt_top hfinite
  have hEt : (momentDualEnergy μ φ).toReal ≤ K := by
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hE
    simpa only [ENNReal.toReal_ofReal hK] using ht
  let C := a * ‖x‖ - φ x
  by_cases hC : C ≤ 0
  · have hdiv : 0 ≤ K / m := div_nonneg hK hm.le
    dsimp only [C] at hC
    linarith
  have hC0 : 0 ≤ C := (lt_of_not_ge hC).le
  have hdom : ∀ᵐ p ∂μ, C * β p ≤ (normalizedLegendreTransform φ p).toReal := by
    filter_upwards [hAE] with p hp
    by_cases hb : β p = 0
    · simp only [hb, mul_zero]
      exact ENNReal.toReal_nonneg
    have hy := normalizedLegendreTransform_young φ hp.ne x
    have hc := hcap p hb
    have hCφ : C ≤ (normalizedLegendreTransform φ p).toReal := by
      dsimp only [C]
      linarith
    exact (mul_le_mul_of_nonneg_left (hβ1 p) hC0).trans (by simpa using hCφ)
  have hi := integral_mono_ae (hβ.const_mul C) hI hdom
  rw [integral_const_mul, integral_normalizedLegendreTransform_toReal hfinite] at hi
  have hCm : C * m ≤ K :=
    (mul_le_mul_of_nonneg_left hβmass hC0).trans (hi.trans hEt)
  have hbound : C ≤ K / m := (le_div_iff₀ hm).mpr (by simpa only [mul_comm] using hCm)
  dsimp only [C] at hbound
  linarith

theorem exists_coordinate_norm_control (hn : 1 ≤ n) (x : Space n) :
    ∃ i : Fin n, ‖x‖ ≤ (n : ℝ) * |x i| := by
  by_contra h
  push_neg at h
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, by omega⟩, by simp⟩
  have hs := Finset.sum_lt_sum_of_nonempty hne (fun i _ => h i)
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hbase := mul_le_mul_of_nonneg_left (norm_le_sum_abs_coordinates x) hn0.le
  simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hs
  linarith

def axisCapCenter (a : ℝ) (i : Fin n × Bool) : Space n :=
  (if i.2 then (n : ℝ) * (a + 1) else -((n : ℝ) * (a + 1))) •
    EuclideanSpace.single i.1 1

theorem axis_caps_separate (hn : 1 ≤ n) {a : ℝ} (ha : 0 ≤ a) (x : Space n) :
    ∃ i : Fin n × Bool, ∀ p ∈ ball (axisCapCenter a i) 1,
      a * ‖x‖ ≤ inner ℝ p x := by
  obtain ⟨i, hi⟩ := exists_coordinate_norm_control hn x
  have hni : (a + 1) * ‖x‖ ≤ ((n : ℝ) * (a + 1)) * |x i| := by
    nlinarith [mul_le_mul_of_nonneg_left hi (show 0 ≤ a + 1 by linarith)]
  obtain ⟨b, hb⟩ : ∃ b : Bool,
      (a + 1) * ‖x‖ ≤ inner ℝ (axisCapCenter a (i, b)) x := by
    by_cases hxi : 0 ≤ x i
    · refine ⟨true, ?_⟩
      simpa only [axisCapCenter, if_true, inner_smul_left, EuclideanSpace.inner_single_left,
        conj_trivial, one_mul, abs_of_nonneg hxi] using hni
    · refine ⟨false, ?_⟩
      have hxi' : x i ≤ 0 := (lt_of_not_ge hxi).le
      simpa only [axisCapCenter, Bool.false_eq_true, if_false, inner_smul_left,
        EuclideanSpace.inner_single_left, conj_trivial, one_mul, abs_of_nonpos hxi', neg_mul,
        mul_neg] using hni
  refine ⟨(i, b), fun p hp => ?_⟩
  have hd : ‖p - axisCapCenter a (i, b)‖ ≤ 1 := by
    exact (mem_ball_iff_norm.mp hp).le
  have he := abs_real_inner_le_norm (p - axisCapCenter a (i, b)) x
  rw [inner_sub_left] at he
  have hnorm := mul_le_mul_of_nonneg_right hd (norm_nonneg x)
  have habs := (neg_le_abs (inner ℝ p x - inner ℝ (axisCapCenter a (i, b)) x)).trans he
  nlinarith

theorem eventual_positive_finite_bump_masses {ι : Type*} [Fintype ι]
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {ν : ℕ → Measure (Space n)} (c : ι → Space n)
    (hfull : ∀ p : Space n, 0 < μ (ball p 1))
    (hlim : ∀ f : Space n → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun k => ∫ p, f p ∂ν k) atTop (𝓝 (∫ p, f p ∂μ))) :
    ∃ (β : ι → Space n → ℝ) (m : ℝ), 0 < m ∧
      (∀ i, Continuous (β i) ∧ HasCompactSupport (β i) ∧
        (∀ p, 0 ≤ β i p ∧ β i p ≤ 1) ∧ Function.support (β i) = ball (c i) 1) ∧
      ∀ᶠ k in atTop, ∀ i, m ≤ ∫ p, β i p ∂ν k := by
  let b (i : ι) : ContDiffBump (c i) := ⟨1/2, 1, by norm_num, by norm_num⟩
  let β (i : ι) : Space n → ℝ := b i
  have hi (i : ι) : Integrable (β i) μ := (b i).continuous.integrable_of_hasCompactSupport
    (b i).hasCompactSupport
  have hp (i : ι) : 0 < ∫ p, β i p ∂μ := by
    rw [integral_pos_iff_support_of_nonneg (fun p => (b i).nonneg) (hi i)]
    simpa only [β, ContDiffBump.support_eq] using hfull (c i)
  let e (i : ι) := (∫ p, β i p ∂μ) / 2
  obtain ⟨m, hm, hb⟩ := (Set.finite_range e).isCompact.exists_forall_le'
    continuous_id.continuousOn (a := 0) (by
      rintro y ⟨i, rfl⟩
      exact half_pos (hp i))
  refine ⟨β, m, hm, ?_, ?_⟩
  · intro i
    exact ⟨(b i).continuous, (b i).hasCompactSupport,
      fun p => ⟨(b i).nonneg, (b i).le_one⟩, (b i).support_eq⟩
  · apply Filter.eventually_all.mpr
    intro i
    have he : e i < ∫ p, β i p ∂μ := half_lt_self (hp i)
    filter_upwards [(tendsto_order.1
      (hlim (β i) (b i).continuous (b i).hasCompactSupport)).1 (e i) he] with k hk
    exact (hb _ (mem_range_self i)).trans hk.le

theorem uniform_cones_of_fullsupport_target_limit (hn : 1 ≤ n)
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {ν : ℕ → Measure (Space n)} [∀ k, IsProbabilityMeasure (ν k)]
    {φ : ℕ → Space n → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hE : ∀ k, momentDualEnergy (ν k) (φ k) ≤ ENNReal.ofReal K)
    (hfull : ∀ p : Space n, 0 < μ (ball p 1))
    (hlim : ∀ f : Space n → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun k => ∫ p, f p ∂ν k) atTop (𝓝 (∫ p, f p ∂μ)))
    {a : ℝ} (ha : 0 ≤ a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop, ∀ x, a * ‖x‖ - B ≤ φ k x := by
  obtain ⟨β, m, hm, hβ, hmass⟩ :=
    eventual_positive_finite_bump_masses (axisCapCenter (n := n) a) hfull hlim
  refine ⟨K / m, div_nonneg hK hm.le, ?_⟩
  filter_upwards [hmass] with k hk x
  obtain ⟨i, hcap⟩ := axis_caps_separate hn ha x
  apply dual_cap_barrier hK hm (hE k)
    ((hβ i).1.integrable_of_hasCompactSupport (hβ i).2.1)
    (fun p => ((hβ i).2.2.1 p).1) (fun p => ((hβ i).2.2.1 p).2) (hk i) x
  intro p hp
  exact hcap p (by rwa [← (hβ i).2.2.2])

end KLSConstantImprovement.ActualDualCapCoercivity405
#print axioms KLSConstantImprovement.ActualDualCapCoercivity405.dual_cap_barrier
#print axioms KLSConstantImprovement.ActualDualCapCoercivity405.exists_coordinate_norm_control
#print axioms KLSConstantImprovement.ActualDualCapCoercivity405.axis_caps_separate
#print axioms KLSConstantImprovement.ActualDualCapCoercivity405.eventual_positive_finite_bump_masses
#print axioms KLSConstantImprovement.ActualDualCapCoercivity405.uniform_cones_of_fullsupport_target_limit

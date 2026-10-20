import KLSConstantImprovement.ActualSmoothScalarTruncation405
import KLS.WeightedFaithfulCutoff

/-! Strong L2 convergence of the concrete value truncations and their
bounded derivative multipliers, on the actual source measure or any
measure on the source space. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal NNReal
namespace KLSConstantImprovement.ActualScalarTruncationL2405
open KLS ActualSmoothScalarTruncation405
variable {n : ℕ} {ρ : Measure (Space n)}

theorem strong_L2_zero_of_pointwise_norm_bound
    {g : ℕ → Space n → ℝ} {a : Space n → ℝ}
    (hgm : ∀ k, AEStronglyMeasurable (g k) ρ) (ha : MemLp a 2 ρ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ k x, ‖g k x‖ ≤ C * ‖a x‖)
    (ht : ∀ x, Tendsto (fun k => g k x) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (g k) 2 ρ) atTop (𝓝 0) := by
  have hmem (k : ℕ) : MemLp (g k) 2 ρ :=
    (ha.const_mul C).mono (hgm k) (Eventually.of_forall fun x => by
      change ‖g k x‖ ≤ ‖C * a x‖
      rw [norm_mul, Real.norm_of_nonneg hC]
      exact hb k x)
  have hbSq (k : ℕ) (x : Space n) : ‖g k x ^ 2‖ ≤ C ^ 2 * a x ^ 2 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hs := (sq_le_sq₀ (norm_nonneg (g k x))
      (mul_nonneg hC (norm_nonneg (a x)))).mpr (hb k x)
    simpa only [mul_pow, Real.norm_eq_abs, sq_abs] using hs
  apply tendsto_eLpNorm_zero_of_integral_sq hmem
  have hd := tendsto_integral_of_dominated_convergence (fun x => C ^ 2 * a x ^ 2)
    (fun k => (hgm k).pow 2) (ha.integrable_sq.const_mul (C ^ 2))
    (fun k => Eventually.of_forall (hbSq k))
    (Eventually.of_forall fun x => by simpa using (ht x).pow 2)
  simpa using hd

theorem scalarClip_comp_memLp {f : Space n → ℝ} (hf : MemLp f 2 ρ) (k : ℕ) :
    MemLp (scalarClip k ∘ f) 2 ρ :=
  hf.mono ((scalarClip_contDiff k).continuous.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (Eventually.of_forall fun x => scalarClip_norm_le k (f x))

theorem scalarClip_comp_strong_L2 {f : Space n → ℝ} (hf : MemLp f 2 ρ) :
    Tendsto (fun k => eLpNorm ((scalarClip k ∘ f) - f) 2 ρ) atTop (𝓝 0) := by
  apply strong_L2_zero_of_pointwise_norm_bound
    (fun k => (scalarClip_comp_memLp hf k).aestronglyMeasurable.sub hf.aestronglyMeasurable)
    hf (show 0 ≤ (2 : ℝ) by norm_num)
  · intro k x
    change ‖scalarClip k (f x) - f x‖ ≤ 2 * ‖f x‖
    calc
      _ ≤ ‖scalarClip k (f x)‖ + ‖f x‖ := norm_sub_le _ _
      _ ≤ ‖f x‖ + ‖f x‖ := add_le_add (scalarClip_norm_le k (f x)) le_rfl
      _ = _ := by ring
  · intro x
    apply tendsto_const_nhds.congr'
    filter_upwards [scalarClip_eventually_identity (f x)] with k hk
    change 0 = scalarClip k (f x) - f x
    rw [hk.1, sub_self]

theorem scalarClip_deriv_comp_top {f : Space n → ℝ}
    (hf : AEStronglyMeasurable f ρ) (k : ℕ) :
    MemLp (deriv (scalarClip k) ∘ f) ∞ ρ := by
  obtain ⟨B, _, hB⟩ := scalarClip_uniform_deriv_bound
  have hc : Continuous (deriv (scalarClip k)) :=
    ((scalarClip_contDiff k).of_le (by norm_num) : ContDiff ℝ 1 (scalarClip k)).continuous_deriv_one
  exact memLp_top_of_bound (hc.comp_aestronglyMeasurable hf) B
    (Eventually.of_forall fun x => hB k (f x))

theorem scalarClip_deriv_multiplier_strong_L2 {f a : Space n → ℝ}
    (hf : AEStronglyMeasurable f ρ) (ha : MemLp a 2 ρ) :
    Tendsto (fun k => eLpNorm
      ((fun x => deriv (scalarClip k) (f x) * a x) - a) 2 ρ) atTop (𝓝 0) := by
  obtain ⟨B, hB0, hB⟩ := scalarClip_uniform_deriv_bound
  have hprod (k : ℕ) : MemLp (fun x => deriv (scalarClip k) (f x) * a x) 2 ρ :=
    (scalarClip_deriv_comp_top hf k).mul ha
  apply strong_L2_zero_of_pointwise_norm_bound
    (fun k => (hprod k).aestronglyMeasurable.sub ha.aestronglyMeasurable)
    ha (show 0 ≤ B + 1 by linarith)
  · intro k x
    change ‖deriv (scalarClip k) (f x) * a x - a x‖ ≤ (B + 1) * ‖a x‖
    calc
      _ ≤ ‖deriv (scalarClip k) (f x) * a x‖ + ‖a x‖ := norm_sub_le _ _
      _ = ‖deriv (scalarClip k) (f x)‖ * ‖a x‖ + ‖a x‖ := by rw [norm_mul]
      _ ≤ B * ‖a x‖ + ‖a x‖ := add_le_add
        (mul_le_mul_of_nonneg_right (hB k (f x)) (norm_nonneg _)) le_rfl
      _ = _ := by ring
  · intro x
    apply tendsto_const_nhds.congr'
    filter_upwards [scalarClip_eventually_identity (f x)] with k hk
    change 0 = deriv (scalarClip k) (f x) * a x - a x
    rw [hk.2, one_mul, sub_self]

end KLSConstantImprovement.ActualScalarTruncationL2405

#print axioms KLSConstantImprovement.ActualScalarTruncationL2405.strong_L2_zero_of_pointwise_norm_bound
#print axioms KLSConstantImprovement.ActualScalarTruncationL2405.scalarClip_comp_strong_L2
#print axioms KLSConstantImprovement.ActualScalarTruncationL2405.scalarClip_deriv_comp_top
#print axioms KLSConstantImprovement.ActualScalarTruncationL2405.scalarClip_deriv_multiplier_strong_L2

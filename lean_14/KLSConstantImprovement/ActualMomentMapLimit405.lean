import KLS.BoundedMomentMapExistence
import KLS.MomentExponentialTails
import KLS.WeightedCaccioppoli

/-! Actual normalized exponential-density / moment-map passage to a C1 limit.
A common genuine linear cone gives dominated convergence of the partition
and every bounded continuous transported test. Thus the limiting source's
pushforward is proved, not a supplied realization certificate. -/
noncomputable section
open MeasureTheory Filter Set InnerProductSpace
open scoped Topology NNReal
namespace KLSConstantImprovement.ActualMomentMapLimit405
open KLS
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem limit_linear_cone {f : ℕ → Space n → ℝ} {φ : Space n → ℝ}
    {a A : ℝ} (hc : ∀ k x, a * ‖x‖ - A ≤ f k x)
    (hlim : ∀ x, Tendsto (fun k => f k x) atTop (𝓝 (φ x))) :
    ∀ x, a * ‖x‖ - A ≤ φ x := by
  intro x
  exact ge_of_tendsto (hlim x) (Eventually.of_forall fun k => hc k x)

theorem tendsto_partition_of_common_linear_cone
    {f : ℕ → Space n → ℝ} {φ : Space n → ℝ}
    (hf : ∀ k, Continuous (f k)) {a A : ℝ} (ha : 0 < a)
    (hc : ∀ k x, a * ‖x‖ - A ≤ f k x)
    (hlim : ∀ x, Tendsto (fun k => f k x) atTop (𝓝 (φ x))) :
    Tendsto (fun k => momentPartitionFunction (f k)) atTop (𝓝 (momentPartitionFunction φ)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun x : Space n => Real.exp A * Real.exp (-a * ‖x‖))
  · intro k
    exact Real.continuous_exp.comp_aestronglyMeasurable (hf k).aestronglyMeasurable.neg
  · exact (integrable_exp_neg_mul_norm n ha).const_mul _
  · intro k
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith only [hc k x]
  · exact Eventually.of_forall fun x => Real.continuous_exp.continuousAt.tendsto.comp (hlim x).neg

theorem normalized_moment_pairing_eq {φ : Space n → ℝ} (hφ : Continuous φ)
    (hi : Integrable (fun x => Real.exp (-φ x)) volume) (v : Space n → ℝ) :
    (∫ x, v (gradient (normalizedMomentPotential φ) x)
      ∂potentialMeasure (normalizedMomentPotential φ)) =
      (∫ x, Real.exp (-φ x) * v (gradient φ x)) / momentPartitionFunction φ := by
  have hp : 0 < momentPartitionFunction φ := integral_exp_pos hi
  have hm : Measurable (normalizedMomentPotential φ) := by
    change Measurable (fun x : Space n => φ x + Real.log (momentPartitionFunction φ))
    exact (hφ.add_const (Real.log (momentPartitionFunction φ))).measurable
  rw [integral_potentialMeasure hm]
  simp_rw [gradient_normalizedMomentPotential]
  calc
    _ = ∫ x, (Real.exp (-φ x) * v (gradient φ x)) / momentPartitionFunction φ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [exp_neg_normalizedMomentPotential hp]
        ring
    _ = _ := integral_div _ _

theorem tendsto_normalized_moment_pairing
    {f : ℕ → Space n → ℝ} {φ : Space n → ℝ}
    (hf : ∀ k, ContDiff ℝ 1 (f k)) (hφ : ContDiff ℝ 1 φ)
    {a A : ℝ} (ha : 0 < a) (hc : ∀ k x, a * ‖x‖ - A ≤ f k x)
    (hlim : ∀ x, Tendsto (fun k => f k x) atTop (𝓝 (φ x)))
    (hg : ∀ x, Tendsto (fun k => gradient (f k) x) atTop (𝓝 (gradient φ x)))
    {v : Space n → ℝ} (hv : Continuous v) {B : ℝ} (hb : ∀ y, |v y| ≤ B) :
    Tendsto (fun k => ∫ x, v (gradient (normalizedMomentPotential (f k)) x)
      ∂potentialMeasure (normalizedMomentPotential (f k))) atTop
      (𝓝 (∫ x, v (gradient (normalizedMomentPotential φ) x)
        ∂potentialMeasure (normalizedMomentPotential φ))) := by
  have hi (k : ℕ) := integrable_exp_neg_of_linear_coercivity (hf k).continuous.aestronglyMeasurable ha (hc k)
  have hiφ := integrable_exp_neg_of_linear_coercivity hφ.continuous.aestronglyMeasurable ha
    (limit_linear_cone hc hlim)
  have hz := tendsto_partition_of_common_linear_cone (fun k => (hf k).continuous) ha hc hlim
  have hzφ : 0 < momentPartitionFunction φ := integral_exp_pos hiφ
  have hB : 0 ≤ B := (abs_nonneg (v 0)).trans (hb 0)
  have hn : Tendsto (fun k => ∫ x, Real.exp (-f k x) * v (gradient (f k) x)) atTop
      (𝓝 (∫ x, Real.exp (-φ x) * v (gradient φ x))) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x : Space n => B * (Real.exp A * Real.exp (-a * ‖x‖)))
    · intro k
      exact ((Real.continuous_exp.comp (hf k).continuous.neg).mul
        (hv.comp (continuous_gradient_of_contDiff (hf k)))).aestronglyMeasurable
    · exact ((integrable_exp_neg_mul_norm n ha).const_mul (Real.exp A)).const_mul B
    · intro k
      exact Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        have he : Real.exp (-f k x) ≤ Real.exp A * Real.exp (-a * ‖x‖) := by
          rw [← Real.exp_add]
          exact Real.exp_le_exp.mpr (by linarith only [hc k x])
        calc
          Real.exp (-f k x) * |v (gradient (f k) x)| ≤ Real.exp (-f k x) * B :=
            mul_le_mul_of_nonneg_left (hb _) (Real.exp_pos _).le
          _ ≤ (Real.exp A * Real.exp (-a * ‖x‖)) * B := mul_le_mul_of_nonneg_right he hB
          _ = _ := mul_comm _ _
    · exact Eventually.of_forall fun x =>
        (Real.continuous_exp.continuousAt.tendsto.comp (hlim x).neg).mul
          (hv.continuousAt.tendsto.comp (hg x))
  have ht := hn.div hz hzφ.ne'
  simpa only [normalized_moment_pairing_eq (hf _).continuous (hi _) v,
    normalized_moment_pairing_eq hφ.continuous hiφ v, Pi.div_def] using ht

theorem gradient_pushforward_normalized_limit
    {ρ : ℕ → Measure (Space n)} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {f : ℕ → Space n → ℝ} {φ : Space n → ℝ}
    (hf : ∀ k, ContDiff ℝ 1 (f k)) (hφ : ContDiff ℝ 1 φ)
    {a A : ℝ} (ha : 0 < a) (hc : ∀ k x, a * ‖x‖ - A ≤ f k x)
    (hlim : ∀ x, Tendsto (fun k => f k x) atTop (𝓝 (φ x)))
    (hg : ∀ x, Tendsto (fun k => gradient (f k) x) atTop (𝓝 (gradient φ x)))
    (hmap : ∀ k, (potentialMeasure (normalizedMomentPotential (f k))).map
      (gradient (normalizedMomentPotential (f k))) = ρ k)
    (hweak : ∀ v : BoundedContinuousFunction (Space n) ℝ,
      Tendsto (fun k => ∫ y, v y ∂ρ k) atTop (𝓝 (∫ y, v y ∂μ))) :
    (potentialMeasure (normalizedMomentPotential φ)).map
      (gradient (normalizedMomentPotential φ)) = μ := by
  have hiφ := integrable_exp_neg_of_linear_coercivity hφ.continuous.aestronglyMeasurable ha
    (limit_linear_cone hc hlim)
  letI := isProbabilityMeasure_normalizedMomentPotential hiφ
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro v
  rw [integral_map (measurable_gradient _).aemeasurable v.continuous.aestronglyMeasurable]
  have ht := tendsto_normalized_moment_pairing hf hφ ha hc hlim hg v.continuous
    (fun y => by simpa only [Real.norm_eq_abs] using v.norm_coe_le_norm y)
  have he (k : ℕ) : (∫ x, v (gradient (normalizedMomentPotential (f k)) x)
      ∂potentialMeasure (normalizedMomentPotential (f k))) = ∫ y, v y ∂ρ k := by
    rw [← hmap k, integral_map (measurable_gradient _).aemeasurable v.continuous.aestronglyMeasurable]
  simp_rw [he] at ht
  exact tendsto_nhds_unique ht (hweak v)

end KLSConstantImprovement.ActualMomentMapLimit405
#print axioms KLSConstantImprovement.ActualMomentMapLimit405.tendsto_partition_of_common_linear_cone
#print axioms KLSConstantImprovement.ActualMomentMapLimit405.normalized_moment_pairing_eq
#print axioms KLSConstantImprovement.ActualMomentMapLimit405.tendsto_normalized_moment_pairing
#print axioms KLSConstantImprovement.ActualMomentMapLimit405.gradient_pushforward_normalized_limit

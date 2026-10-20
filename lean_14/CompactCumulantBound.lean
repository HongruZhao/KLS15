import KLS.CumulantApriori

/-! All cumulant orders are uniformly bounded on probability laws supported
in one fixed ball. The finite Faà di Bruno majorant reuses the released
proof, with bounded-source moments replacing isotropic tail moments. -/

open MeasureTheory Set Filter Metric
open scoped Topology ContDiff BigOperators
noncomputable section
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ}

def compactCumulantBound (R : ℝ) (m : ℕ) : ℝ :=
  ∑ c : OrderedFinpartition m,
    ‖iteratedFDeriv ℝ c.length Real.log 1‖ * ∏ j, R ^ (c.partSize j)

theorem compactCumulantBound_nonneg {R : ℝ} (hR : 0 ≤ R) (m : ℕ) :
    0 ≤ compactCumulantBound R m := by
  unfold compactCumulantBound
  exact Finset.sum_nonneg fun c _ => mul_nonneg (norm_nonneg _)
    (Finset.prod_nonneg fun j _ => pow_nonneg hR _)

theorem integral_norm_pow_le_of_support_ball
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hc : IsCompact μ.support) {R : ℝ} (hR : 0 ≤ R)
    (hball : μ.support ⊆ closedBall (0 : Space n) R) (d : ℕ) :
    (∫ x, ‖x‖ ^ d ∂μ) ≤ R ^ d := by
  calc
    _ ≤ ∫ _ : Space n, R ^ d ∂μ := by
      apply integral_mono_ae
        (integrable_of_continuous_compact_support_measure hc (by fun_prop))
        (integrable_const _)
      filter_upwards [μ.support_mem_ae] with x hx
      exact pow_le_pow_left₀ (norm_nonneg x) (by simpa using hball hx) d
    _ = _ := by simp

theorem norm_cumulantTensor_le_of_support_ball
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hc : IsCompact μ.support) {R : ℝ} (hR : 0 ≤ R)
    (hball : μ.support ⊆ closedBall (0 : Space n) R) (m : ℕ) :
    ‖cumulantTensor μ m‖ ≤ compactCumulantBound R m := by
  let Z := tiltNumerator μ (fun _ => 0) (fun _ => 1)
  have hZ : ContDiff ℝ (⊤ : ℕ∞) Z :=
    contDiff_tiltNumerator hc continuous_const (integrable_const (1 : ℝ))
  have hZ0 : Z 0 = 1 := by simp [Z, tiltNumerator]
  have hlog : tiltLogLaplace μ = Real.log ∘ Z := by
    funext z
    simp [tiltLogLaplace, tiltPartition, Z, tiltNumerator]
  have hJ (d : ℕ) : ‖iteratedFDeriv ℝ d Z 0‖ ≤ R ^ d := by
    calc
      _ ≤ ∫ x, ‖(1 : ℝ)‖ * ‖x‖ ^ d ∂μ :=
        norm_iteratedFDeriv_tiltNumerator_le_moment
          (normExponentialDomain_const_one_of_compact hc)
      _ = ∫ x, ‖x‖ ^ d ∂μ := by simp
      _ ≤ _ := integral_norm_pow_le_of_support_ball hc hR hball d
  have hgl : ContDiffAt ℝ m Real.log (Z 0) := by
    rw [hZ0]
    exact Real.contDiffAt_log.mpr (by norm_num)
  unfold cumulantTensor
  rw [hlog, iteratedFDeriv_comp hgl (hZ.contDiffAt.of_le (by simp)) le_rfl, hZ0]
  unfold FormalMultilinearSeries.taylorComp compactCumulantBound
  calc
    _ ≤ ∑ c : OrderedFinpartition m,
        ‖(ftaylorSeries ℝ Real.log 1).compAlongOrderedFinpartition (ftaylorSeries ℝ Z 0) c‖ :=
      norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro c _
      apply (c.norm_compAlongOrderedFinpartition_le _ _).trans
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hJ _)

/-- The same majorant works for every continuous tilt, without any isotropy
or log-concavity assumption on those posterior laws. -/
theorem norm_cumulantTensor_tilted_le_of_support_ball
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hc : IsCompact μ.support) {R : ℝ} (hR : 0 ≤ R)
    (hball : μ.support ⊆ closedBall (0 : Space n) R)
    {q : Space n → ℝ} (hq : Continuous q) (m : ℕ) :
    ‖cumulantTensor (μ.tilted q) m‖ ≤ compactCumulantBound R m := by
  have := tilted_isProbability_of_compact_support hc hq
  apply norm_cumulantTensor_le_of_support_ball
    (by rwa [tilted_support_eq hc hq]) hR
    (by rwa [tilted_support_eq hc hq])

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.norm_cumulantTensor_le_of_support_ball
#print axioms KLS.DeterministicBridgeIntegration.norm_cumulantTensor_tilted_le_of_support_ball

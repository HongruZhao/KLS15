import KLSConstantImprovement.ActualWeakCanonicalMetricResponse

/-! The actual scalar response is bounded by its vector's H-weighted
energy using only the first-order canonical form. No connection charge,
second derivative or boundary theorem for a general L2 response forcing
is needed for this upper bound. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators RealInnerProductSpace
namespace KLSConstantImprovement.ActualResponseWeightedEnergy405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualWeakCanonicalMetricOrdinaryGraph ActualWeakCanonicalMetricInverse
open ActualWeakCanonicalMetricResponse
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

def sourceResponseWeightedRow (d : SourceData μ)
    (e : Fin n → Lp ℝ 2 (potentialMeasure d.potential)) (j : Fin n) :
    Lp ℝ 2 (potentialMeasure d.potential) := ∑ i, sourceUnrootMultiplier d i j (e i)

theorem sourceUnrootMultiplier_inner (d : SourceData μ) (i j : Fin n)
    (f g : Lp ℝ 2 (potentialMeasure d.potential)) :
    inner ℝ f (sourceUnrootMultiplier d i j g) =
      inner ℝ (sourceUnrootMultiplier d i j f) g := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sourceUnrootMultiplier_coe d i j f, sourceUnrootMultiplier_coe d i j g]
    with x hf hg
  simp only [RCLike.inner_apply, conj_trivial, hf, hg]
  ring

theorem actual_response_weighted_functional (d : SourceData μ)
    (e : Fin n → Lp ℝ 2 (potentialMeasure d.potential))
    (U : CanonicalMetricH1 d.potential) :
    sourceResponseFunctional d e U = ∑ j, inner ℝ (sourceResponseWeightedRow d e j)
      (canonicalMetricGradient d.potential j U) := by
  rw [sourceResponseFunctional_apply]
  simp_rw [sourceOrdinaryH1Embedding_derivative, inner_sum, sourceUnrootMultiplier_inner]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [sourceResponseWeightedRow, sum_inner]

theorem actual_response_energy_le_weighted_rows (d : SourceData μ)
    (e : Fin n → Lp ℝ 2 (potentialMeasure d.potential)) :
    canonicalMetricEnergy d.potential (sourceResponseH1 d e) (sourceResponseH1 d e) ≤
      ∑ j, ‖sourceResponseWeightedRow d e j‖ ^ 2 := by
  let U := sourceResponseH1 d e
  let v : PiLp 2 (fun _ : Fin n => Lp ℝ 2 (potentialMeasure d.potential)) :=
    WithLp.toLp 2 (sourceResponseWeightedRow d e)
  let w : PiLp 2 (fun _ : Fin n => Lp ℝ 2 (potentialMeasure d.potential)) :=
    WithLp.toLp 2 (fun j => canonicalMetricGradient d.potential j U)
  have hw : ‖w‖ ^ 2 = canonicalMetricEnergy d.potential U U := by
    rw [PiLp.norm_sq_eq_of_L2, canonicalMetricEnergy_apply]
    simp only [w, PiLp.toLp_apply, real_inner_self_eq_norm_sq]
  have hv : ‖v‖ ^ 2 = ∑ j, ‖sourceResponseWeightedRow d e j‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
  have hp : inner ℝ v w = canonicalMetricEnergy d.potential U U := by
    rw [sourceResponse_variational, actual_response_weighted_functional]
    rfl
  have hc := real_inner_le_norm v w
  rw [hp, ← hw] at hc
  have hn : ‖w‖ ≤ ‖v‖ := by
    by_cases hz : ‖w‖ = 0
    · rw [hz]; exact norm_nonneg v
    · have hwpos := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hz)
      nlinarith
  have hs := pow_le_pow_left₀ (norm_nonneg w) hn 2
  rw [hw, hv] at hs
  exact hs

theorem actual_response_norm_le_weighted_rows (d : SourceData μ)
    (e : Fin n → Lp ℝ 2 (potentialMeasure d.potential)) :
    ‖sourceResponse d e‖ ^ 2 ≤ ∑ j, ‖sourceResponseWeightedRow d e j‖ ^ 2 := by
  have he := actual_response_energy_le_weighted_rows d e
  rw [canonicalMetricEnergy_self] at he
  exact (sourceMetricValue_norm_sq_le_energy d (sourceResponseH1 d e)).trans he

end KLSConstantImprovement.ActualResponseWeightedEnergy405
#print axioms KLSConstantImprovement.ActualResponseWeightedEnergy405.actual_response_weighted_functional
#print axioms KLSConstantImprovement.ActualResponseWeightedEnergy405.actual_response_energy_le_weighted_rows
#print axioms KLSConstantImprovement.ActualResponseWeightedEnergy405.actual_response_norm_le_weighted_rows

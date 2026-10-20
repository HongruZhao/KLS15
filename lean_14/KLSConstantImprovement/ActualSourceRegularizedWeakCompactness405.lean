import KLSConstantImprovement.ActualSourceRegularizedInverseUniformH1405
import KLS.WeakGradientExtraction

/-!
Actual weak compactness of the scalar regularized inverses in the
ordinary source H1 graph. The measure is fixed; weak derivatives are
coordinates of a closed graph. This is not an operator-core assertion.
-/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceRegularizedWeakCompactness405
open KLS ActualBoundedCanonicalSource ActualSourceRegularizedEnergyForm405
open ActualSourceRegularizedInverseUniformH1405
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem tendsto_real_clm_of_weak_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {U : ℕ → E} {u : E}
    (hw : ∀ v : E, Tendsto (fun k => inner ℝ (U k) v) atTop (𝓝 (inner ℝ u v)))
    (L : E →L[ℝ] ℝ) : Tendsto (fun k => L (U k)) atTop (𝓝 (L u)) := by
  let v := (InnerProductSpace.toDual ℝ E).symm L
  have he (x : E) : inner ℝ x v = L x := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  simpa only [he] using hw v

theorem exists_regularizedOrdinaryInverse_weak_subsequence (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    ∃ (K : ℝ) (U : WeightedCenteredH1 d.potential) (σ : ℕ → ℕ),
      0 < K ∧ StrictMono σ ∧ ‖U‖ ≤ K * ‖g‖ ∧
      ∀ L : WeightedCenteredH1 d.potential →L[ℝ] ℝ,
        Tendsto (fun r => L (regularizedOrdinaryInverse d hn (σ r) (cutoffScale_pos (σ r)) g))
          atTop (𝓝 (L U)) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  letI : TopologicalSpace.SeparableSpace (Lp ℝ 2 (potentialMeasure d.potential)) := inferInstance
  letI : TopologicalSpace.SeparableSpace (WeightedEnergyAmbient d.potential) := inferInstance
  letI : TopologicalSpace.SeparableSpace (WeightedCenteredH1 d.potential) := inferInstance
  obtain ⟨K, hK, hb⟩ := exists_regularizedOrdinaryInverse_uniform_H1_bound d hn
  have hbound (k : ℕ) : ‖regularizedOrdinaryInverse d hn k (cutoffScale_pos k) g‖ ≤ K * ‖g‖ := by
    apply hb k (cutoffScale k) (cutoffScale_pos k) _ g
    unfold cutoffScale
    apply inv_le_one_of_one_le₀
    linarith [Nat.cast_nonneg (α := ℝ) k]
  obtain ⟨U, σ, hσ, hU, hweak⟩ := exists_weak_limit_of_bounded_hilbert hbound
  exact ⟨K, U, σ, hK, hσ, hU, fun L => tendsto_real_clm_of_weak_inner hweak L⟩

end KLSConstantImprovement.ActualSourceRegularizedWeakCompactness405
#print axioms KLSConstantImprovement.ActualSourceRegularizedWeakCompactness405.tendsto_real_clm_of_weak_inner
#print axioms KLSConstantImprovement.ActualSourceRegularizedWeakCompactness405.exists_regularizedOrdinaryInverse_weak_subsequence

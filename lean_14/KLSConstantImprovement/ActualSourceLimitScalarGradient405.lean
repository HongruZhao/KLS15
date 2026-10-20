import KLSConstantImprovement.ActualSourceGradientCompactPairing405
import KLSConstantImprovement.ActualSourceCompactPairSeparation405
import KLSConstantImprovement.ActualFiniteFamilyWeakPassage405
import KLSConstantImprovement.ActualHilbertWeakPassage405

/-! The genuine ordinary weak gradient of the constructed scalar limit
is the original Hessian root applied to the common mass-energy limit. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceLimitScalarGradient405
open KLS ActualBoundedCanonicalSource ActualSourceRegularizedEnergyVector405
open ActualSourceRegularizedFluxH1405 ActualSourceRegularizedEnergyForm405
open ActualSourceGradientCoefficientPassage405 ActualSourceGradientCompactPairing405
open ActualSourceLimitFluxDomains405 ActualSourceLimitFluxPairing405
open ActualSourceCompactPairSeparation405 ActualFiniteFamilyWeakPassage405 ActualHilbertWeakPassage405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem energyLimitScalarGradient_compact_pair_tendsto (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (D : ℕ → Fin n → Fin n → Space n → ℝ) (W : ℕ → GaffneyEnergyAmbient d)
    (V : GaffneyEnergyAmbient d) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (hW : ∀ k a, (W k a : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      regularizedGaffneyEnergyField d hn k (cutoffScale_pos k) g (D k) a)
    {M : ℝ} (hbound : ∀ k, ‖W k‖ ≤ M)
    (hw : ∀ Y, Tendsto (fun k => inner ℝ (W (σ k)) Y) atTop (𝓝 (inner ℝ V Y)))
    {ψ : Space n → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (i : Fin n) :
    Tendsto (fun r => ∫ x, weightedH1Derivative d.potential i
      (regularizedOrdinaryInverse d hn (σ r) (cutoffScale_pos (σ r)) g) x * ψ x
      ∂potentialMeasure d.potential) atTop
      (𝓝 (∫ x, energyLimitScalarGradient d V i x * ψ x ∂potentialMeasure d.potential)) := by
  have hψ2 := memLp_of_continuous_hasCompactSupport d.source_C1.continuous hψ hc
  have hQ (a : Fin n) := compact_gradient_coefficient_mul_tendsto_L2 d hc i a hψ2
  choose hp hl ht using hQ
  have hpair (a : Fin n) :
      Tendsto (fun r => inner ℝ (W (σ r) (Sum.inl a))
        ((hp a (σ r)).toLp (fun x => compactRegularizedGradientCoefficient d (tsupport ψ) i a (σ r) x * ψ x))) atTop
      (𝓝 (inner ℝ (V (Sum.inl a))
        ((hl a).toLp (fun x => compactActualGradientCoefficient d (tsupport ψ) i a x * ψ x)))) := by
    have hb (r : ℕ) : ‖W (σ r) (Sum.inl a)‖ ≤ M :=
      (PiLp.norm_apply_le (W (σ r)) (Sum.inl a)).trans (hbound (σ r))
    exact inner_tendsto_of_weak_and_strong hb
      (fun Y => finite_family_weak_coordinate_tendsto hw (Sum.inl a) Y)
      ((ht a).comp hσ.tendsto_atTop)
  have hlim := tendsto_finsetSum Finset.univ (fun a _ => hpair a)
  rw [limit_gradient_compact_pair_eq_inner_sum d V hc i hl]
  exact hlim.congr fun r =>
    (regularized_gradient_compact_pair_eq_inner_sum d hn (σ r) g (D (σ r)) (W (σ r))
      (hW (σ r)) hc i (fun a => hp a (σ r))).symm

theorem ordinaryWeakScalarGradient_compact_pair_tendsto (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (U : WeightedCenteredH1 d.potential) (σ : ℕ → ℕ)
    (hU : ∀ L : WeightedCenteredH1 d.potential →L[ℝ] ℝ,
      Tendsto (fun r => L (regularizedOrdinaryInverse d hn (σ r) (cutoffScale_pos (σ r)) g))
        atTop (𝓝 (L U)))
    {ψ : Space n → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (i : Fin n) :
    Tendsto (fun r => ∫ x, weightedH1Derivative d.potential i
      (regularizedOrdinaryInverse d hn (σ r) (cutoffScale_pos (σ r)) g) x * ψ x
      ∂potentialMeasure d.potential) atTop
      (𝓝 (∫ x, weightedH1Derivative d.potential i U x * ψ x ∂potentialMeasure d.potential)) := by
  have hψ2 := memLp_of_continuous_hasCompactSupport d.source_C1.continuous hψ hc
  let z := hψ2.toLp ψ
  let L := (InnerProductSpace.toDual ℝ (Lp ℝ 2 (potentialMeasure d.potential)) z).comp
    (weightedH1Derivative d.potential i)
  have ht := hU L
  change Tendsto (fun r => inner ℝ z (weightedH1Derivative d.potential i
    (regularizedOrdinaryInverse d hn (σ r) (cutoffScale_pos (σ r)) g))) atTop
    (𝓝 (inner ℝ z (weightedH1Derivative d.potential i U))) at ht
  have htr : Tendsto (fun r => inner ℝ (weightedH1Derivative d.potential i
      (regularizedOrdinaryInverse d hn (σ r) (cutoffScale_pos (σ r)) g)) z) atTop
      (𝓝 (inner ℝ (weightedH1Derivative d.potential i U) z)) := by
    simpa only [real_inner_comm] using ht
  rw [integral_lp_mul_eq_inner_toLp (weightedH1Derivative d.potential i U) hψ2]
  exact htr.congr fun r =>
    (integral_lp_mul_eq_inner_toLp
      (weightedH1Derivative d.potential i (regularizedOrdinaryInverse d hn (σ r) (cutoffScale_pos (σ r)) g)) hψ2).symm

theorem ordinaryWeakScalarGradient_eq_energyLimit_ae (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (D : ℕ → Fin n → Fin n → Space n → ℝ) (W : ℕ → GaffneyEnergyAmbient d)
    (U : WeightedCenteredH1 d.potential) (V : GaffneyEnergyAmbient d) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (hW : ∀ k a, (W k a : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      regularizedGaffneyEnergyField d hn k (cutoffScale_pos k) g (D k) a)
    {M : ℝ} (hbound : ∀ k, ‖W k‖ ≤ M)
    (hU : ∀ L : WeightedCenteredH1 d.potential →L[ℝ] ℝ,
      Tendsto (fun r => L (regularizedOrdinaryInverse d hn (σ r) (cutoffScale_pos (σ r)) g))
        atTop (𝓝 (L U)))
    (hw : ∀ Y, Tendsto (fun k => inner ℝ (W (σ k)) Y) atTop (𝓝 (inner ℝ V Y))) (i : Fin n) :
    (weightedH1Derivative d.potential i U : Space n → ℝ) =ᵐ[volume] energyLimitScalarGradient d V i := by
  apply ae_eq_of_source_compact_pairs d.source_C1.continuous
    (KLS.MemLp.locallyIntegrable_volume_of_potentialMeasure (Lp.memLp _) d.source_C1.continuous)
    (KLS.MemLp.locallyIntegrable_volume_of_potentialMeasure
      (energyLimitScalarGradient_memLp d V i) d.source_C1.continuous)
  intro ψ hψ hc
  exact tendsto_nhds_unique
    (ordinaryWeakScalarGradient_compact_pair_tendsto d hn g U σ hU hψ hc i)
    (energyLimitScalarGradient_compact_pair_tendsto d hn g D W V σ hσ hW hbound hw hψ hc i)

end KLSConstantImprovement.ActualSourceLimitScalarGradient405
#print axioms KLSConstantImprovement.ActualSourceLimitScalarGradient405.energyLimitScalarGradient_compact_pair_tendsto
#print axioms KLSConstantImprovement.ActualSourceLimitScalarGradient405.ordinaryWeakScalarGradient_compact_pair_tendsto
#print axioms KLSConstantImprovement.ActualSourceLimitScalarGradient405.ordinaryWeakScalarGradient_eq_energyLimit_ae

import KLSConstantImprovement.ActualSourceLimitScalarGradient405
import KLSConstantImprovement.ActualSourceLimitDivergence405
import KLSConstantImprovement.ActualRawPoissonIdentification405

/-! The constructed joint metric limit is the actual canonical inverse.
Maximal raw form membership and compact form uniqueness are already paid;
this file supplies their genuine weak-gradient, energy and equation data. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceNaturalInverseIdentification405
open KLS ActualBoundedCanonicalSource ActualSourceRegularizedEnergyVector405
open ActualSourceRegularizedFluxH1405 ActualSourceRegularizedEnergyForm405
open ActualSourceLimitFluxDomains405 ActualSourceLimitMetricRelations405
open ActualSourceLimitScalarGradient405 ActualSourceLimitDivergence405 ActualRawPoissonIdentification405
open ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricInverse
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem naturalInverse_eq_joint_scalar_limit (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0)
    (D : ℕ → Fin n → Fin n → Space n → ℝ) (W : ℕ → GaffneyEnergyAmbient d)
    (U : WeightedCenteredH1 d.potential) (V : GaffneyEnergyAmbient d) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (hW : ∀ k a, (W k a : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      regularizedGaffneyEnergyField d hn k (cutoffScale_pos k) g (D k) a)
    {M : ℝ} (hbound : ∀ k, ‖W k‖ ≤ M)
    (hU : ∀ L : WeightedCenteredH1 d.potential →L[ℝ] ℝ,
      Tendsto (fun r => L (regularizedOrdinaryInverse d hn (σ r) (cutoffScale_pos (σ r)) g))
        atTop (𝓝 (L U)))
    (hw : ∀ Y, Tendsto (fun k => inner ℝ (W (σ k)) Y) atTop (𝓝 (inner ℝ V Y))) :
    (sourceMetricInverse d g : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      (weightedH1Value d.potential U : Space n → ℝ) ∧
      ∀ i, (canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g) : Space n → ℝ)
        =ᵐ[potentialMeasure d.potential] (V (Sum.inl i) : Space n → ℝ) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hgrad (i : Fin n) := ordinaryWeakScalarGradient_eq_energyLimit_ae d hn g D W U V σ hσ hW hbound hU hw i
  have hFw (i : Fin n) : HasLocalWeakCoordinateDerivative (weightedH1Value d.potential U)
      (energyLimitScalarGradient d V i) i := by
    have hbase : HasLocalWeakCoordinateDerivative (weightedH1Value d.potential U)
        (weightedH1Derivative d.potential i U) i := by
      intro ψ hψ hc
      exact weightedH1_unweighted_weak_identity d.source_C1 U hψ hc i
    exact hbase.congr_ae EventuallyEq.rfl (hgrad i)
  have hFloc (i : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (energyLimitScalarGradient d V i) 2 (volume.restrict E) :=
    KLS.MemLp.restrict_volume_of_potentialMeasure (energyLimitScalarGradient_memLp d V i) d.source_C1.continuous hE
  obtain ⟨hv, hd⟩ := exists_actual_inverse_of_raw_compact_equation d g hg
    (Lp.memLp (weightedH1Value d.potential U)) hFloc hFw
    (energyLimitScalarGradient_energy_integrable d V)
    (fun ψ hψ hc => energyLimitScalarGradient_compact_raw_equation d hn g hg D W V σ hW hw hψ hc)
  have hmean := weightedH1_integral_eq_zero d.source_C1.continuous U
  refine ⟨?_, fun i => (hd i).trans (energyLimitScalarGradient_raw_metric_ae d V i)⟩
  simpa only [hmean, sub_zero] using hv

end KLSConstantImprovement.ActualSourceNaturalInverseIdentification405
#print axioms KLSConstantImprovement.ActualSourceNaturalInverseIdentification405.naturalInverse_eq_joint_scalar_limit

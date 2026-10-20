import KLSConstantImprovement.ActualSourceJointWeakLimit405
import KLSConstantImprovement.ActualSourceMetricFaithfulness405
import KLSConstantImprovement.ActualSourceRegularizedRootPassage405

/-! Literal flux and Jacobian fields represented by a global Gaffney
energy vector. This file pays their actual compact Lebesgue L2 domains;
the limiting weak derivative identity is proved separately. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceLimitFluxDomains405
open KLS ActualBoundedCanonicalSource ActualSourceRegularizedEnergyVector405
open ActualSourceRegularizedFluxH1405 ActualSourceRegularizedEnergyForm405
open ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricCore ActualWeakCanonicalMetricSmoothing
open ActualWeakCanonicalMetricOrdinaryGraph ActualSourceMetricFaithfulness405
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

def energyLimitFlux (d : SourceData μ) (V : GaffneyEnergyAmbient d)
    (i : Fin n) (x : Space n) : ℝ :=
  ∑ a : Fin n, canonicalMetricRoot d.potential x i a * V (Sum.inl a) x

def energyLimitJacobian (d : SourceData μ) (V : GaffneyEnergyAmbient d)
    (i j : Fin n) (x : Space n) : ℝ :=
  ∑ a : Fin n, ∑ b : Fin n,
    (canonicalMetricRoot d.potential x i a * canonicalMetricUnroot d.potential x b j) * V (Sum.inr (a, b)) x

def energyLimitScalarGradient (d : SourceData μ) (V : GaffneyEnergyAmbient d)
    (i : Fin n) (x : Space n) : ℝ :=
  ∑ a : Fin n, canonicalMetricUnroot d.potential x i a * V (Sum.inl a) x

theorem actualRoot_entry_top_on_compact (d : SourceData μ)
    {E : Set (Space n)} (hE : IsCompact E) (i a : Fin n) :
    MemLp (fun x => canonicalMetricRoot d.potential x i a) ∞ (volume.restrict E) := by
  have hm := KLS.MemLp.restrict_volume_of_potentialMeasure (d.compact_metricRoot_entry_top hE i a)
    d.source_C1.continuous hE
  have he : E.indicator (fun x => canonicalMetricRoot d.potential x i a) =ᵐ[volume.restrict E]
      fun x => canonicalMetricRoot d.potential x i a := by
    filter_upwards [ae_restrict_mem hE.measurableSet] with x hx
    exact indicator_of_mem hx _
  exact (memLp_congr_ae he).mp hm

theorem actualUnroot_entry_memLp_top (d : SourceData μ) (b j : Fin n) :
    MemLp (fun x => canonicalMetricUnroot d.potential x b j) ∞ (potentialMeasure d.potential) := by
  have hm := (continuous_apply j).comp_aestronglyMeasurable
    ((continuous_apply b).comp_aestronglyMeasurable (sourceMetricUnroot_aestronglyMeasurable d))
  exact memLp_top_of_bound hm (16 / d.targetConvexityConstant + 1) (sourceMetricUnroot_entry_bound d b j)

theorem energyLimitFlux_Jacobian_local_L2 (d : SourceData μ) (V : GaffneyEnergyAmbient d)
    {E : Set (Space n)} (hE : IsCompact E) :
    (∀ i, MemLp (energyLimitFlux d V i) 2 (volume.restrict E)) ∧
      ∀ i j, MemLp (energyLimitJacobian d V i j) 2 (volume.restrict E) := by
  have hv (a : GaffneyEnergyIndex n) : MemLp (V a) 2 (volume.restrict E) :=
    KLS.MemLp.restrict_volume_of_potentialMeasure (Lp.memLp _) d.source_C1.continuous hE
  have hs (b j : Fin n) : MemLp (fun x => canonicalMetricUnroot d.potential x b j) ∞ (volume.restrict E) :=
    KLS.MemLp.restrict_volume_of_potentialMeasure (actualUnroot_entry_memLp_top d b j) d.source_C1.continuous hE
  constructor
  · intro i
    exact memLp_finsetSum Finset.univ fun a _ => (actualRoot_entry_top_on_compact d hE i a).mul (hv (Sum.inl a))
  · intro i j
    apply memLp_finsetSum Finset.univ
    intro a _
    apply memLp_finsetSum Finset.univ
    intro b _
    have hc : MemLp (fun x => canonicalMetricRoot d.potential x i a * canonicalMetricUnroot d.potential x b j)
        ∞ (volume.restrict E) := (actualRoot_entry_top_on_compact d hE i a).mul (hs b j)
    exact hc.mul (hv (Sum.inr (a, b)))

theorem energyLimitScalarGradient_memLp (d : SourceData μ) (V : GaffneyEnergyAmbient d) (i : Fin n) :
    MemLp (energyLimitScalarGradient d V i) 2 (potentialMeasure d.potential) := by
  exact memLp_finsetSum Finset.univ fun a _ => (actualUnroot_entry_memLp_top d i a).mul (Lp.memLp _)

theorem regularizedWeakFlux_eq_energyLimitFlux_ae (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (D : Fin n → Fin n → Space n → ℝ) (W : GaffneyEnergyAmbient d)
    (hW : ∀ a, (W a : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      regularizedGaffneyEnergyField d hn k hε g D a) (i : Fin n) :
    regularizedWeakFlux d hn k hε g i =ᵐ[potentialMeasure d.potential] energyLimitFlux d W i := by
  filter_upwards [d.hessian_ae_source, ae_all_iff.mpr hW] with x hx hw
  let R := canonicalMetricRoot d.potential x
  let S := canonicalMetricUnroot d.potential x
  let u := fun a => regularizedWeakFlux d hn k hε g a x
  have hcol : (fun a => W (Sum.inl a) x) = S *ᵥ u := by
    funext a
    exact hw (Sum.inl a)
  have he : R *ᵥ (fun a => W (Sum.inl a) x) = u := by
    rw [hcol, Matrix.mulVec_mulVec, canonicalMetricRoot_mul_unroot_at hx.1, Matrix.one_mulVec]
  exact (congrFun he i).symm

end KLSConstantImprovement.ActualSourceLimitFluxDomains405
#print axioms KLSConstantImprovement.ActualSourceLimitFluxDomains405.actualRoot_entry_top_on_compact
#print axioms KLSConstantImprovement.ActualSourceLimitFluxDomains405.actualUnroot_entry_memLp_top
#print axioms KLSConstantImprovement.ActualSourceLimitFluxDomains405.energyLimitFlux_Jacobian_local_L2
#print axioms KLSConstantImprovement.ActualSourceLimitFluxDomains405.energyLimitScalarGradient_memLp
#print axioms KLSConstantImprovement.ActualSourceLimitFluxDomains405.regularizedWeakFlux_eq_energyLimitFlux_ae

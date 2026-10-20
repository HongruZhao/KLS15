import KLSConstantImprovement.ActualWeakCanonicalMetricCore
import KLSConstantImprovement.ActualCanonicalMetricResolvent

/-!
# Canonical metric inverses on the actually constructed weak source

The C1,1 source is constructed from the original bounded strongly convex
target law. Its actual weak compact metric core supplies all L2 and BL
inputs. This file proves coercivity and constructs the metric inverse on
that same source, without a classical C4 bootstrap, pointwise Hessian
assumption, free coercivity certificate, or assumed Poisson solution.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Set Filter Matrix
open scoped BigOperators ContDiff RealInnerProductSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLSConstantImprovement.ActualWeakCanonicalMetricInverse

open KLS
open KLSConstantImprovement.ActualBoundedCanonicalSource
open KLSConstantImprovement.ActualWeakCanonicalMetricCore
open KLSConstantImprovement.ActualCanonicalMetricEnergyGraph
open KLSConstantImprovement.ActualCanonicalMetricResolvent
variable {n : ℕ} {μ : Measure (Space n)}

theorem exists_sourceMetricH1_of_smoothCompact (d : SourceData μ)
    {f : Space n → ℝ} (hf : ContDiff ℝ 3 f) (hc : HasCompactSupport f) :
    ∃ U : CanonicalMetricH1 d.potential,
      ((canonicalMetricValue d.potential U : Lp ℝ 2 (potentialMeasure d.potential)) : Space n → ℝ)
        =ᵐ[potentialMeasure d.potential]
          (fun x => f x - ∫ y, f y ∂potentialMeasure d.potential) ∧
      ∀ i : Fin n,
        ((canonicalMetricGradient d.potential i U : Lp ℝ 2 (potentialMeasure d.potential)) :
          Space n → ℝ) =ᵐ[potentialMeasure d.potential]
            canonicalMetricDerivative d.potential f i := by
  letI := d.source_probability
  let hf2 := memLp_of_continuous_hasCompactSupport d.source_C1.continuous hf.continuous hc
  let hd2 (i : Fin n) := d.metric_derivative_memLp (hf.of_le (by norm_num)) hc i
  let F : Lp ℝ 2 (potentialMeasure d.potential) := hf2.toLp f
  let G (i : Fin n) : Lp ℝ 2 (potentialMeasure d.potential) :=
    (hd2 i).toLp (canonicalMetricDerivative d.potential f i)
  let W : WeightedEnergyAmbient d.potential :=
    WithLp.toLp 2 (Fin.cases (CenteredL2.center (potentialMeasure d.potential) F) G)
  have hW0 : ((W 0 : Lp ℝ 2 (potentialMeasure d.potential)) : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential]
        (fun x => f x - ∫ y, f y ∂potentialMeasure d.potential) := by
    have hF : (F : Space n → ℝ) =ᵐ[potentialMeasure d.potential] f := hf2.coeFn_toLp
    have hi : (∫ x, F x ∂potentialMeasure d.potential) =
        ∫ x, f x ∂potentialMeasure d.potential := integral_congr_ae hF
    filter_upwards [CenteredL2.center_ae (potentialMeasure d.potential) F, hF] with x hx hy
    change (CenteredL2.center (potentialMeasure d.potential) F) x = _
    rw [hx, hi, hy]
  have hWi (i : Fin n) : ((W i.succ : Lp ℝ 2 (potentialMeasure d.potential)) : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential] canonicalMetricDerivative d.potential f i :=
    (hd2 i).coeFn_toLp
  have hW : W ∈ canonicalMetricGraph d.potential :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, hf, hc, hW0, hWi⟩)
  exact ⟨⟨W, hW⟩, hW0, hWi⟩

private theorem source_core_value_norm_sq_le (d : SourceData μ)
    {U : WeightedEnergyAmbient d.potential} (hU : U ∈ smoothCanonicalMetricGraphSet d.potential) :
    ‖U 0‖ ^ 2 ≤ ∑ i : Fin n, ‖U i.succ‖ ^ 2 := by
  letI := d.source_probability
  obtain ⟨f, hf, hc, hv, hd⟩ := hU
  have hvnorm : ‖U 0‖ ^ 2 = ProbabilityTheory.variance f (potentialMeasure d.potential) := by
    rw [ProbabilityTheory.variance_eq_integral hf.continuous.aemeasurable,
      ← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    simp [hx, pow_two]
  have hd2 (i : Fin n) := d.metric_derivative_memLp (hf.of_le (by norm_num)) hc i
  have hdnorm (i : Fin n) : ‖U i.succ‖ ^ 2 =
      ∫ x, canonicalMetricDerivative d.potential f i x ^ 2 ∂potentialMeasure d.potential := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hd i] with x hx
    simp [hx, pow_two]
  rw [hvnorm]
  simp_rw [hdnorm]
  rw [← integral_finsetSum Finset.univ (fun i _ => (hd2 i).integrable_sq)]
  rw [integral_congr_ae (d.metric_derivative_sq_ae f)]
  exact d.compact_brascampLieb (hf.of_le (by norm_num)) hc

/-- BL coercivity is proved on the completed graph of this actual source. -/
theorem sourceMetricValue_norm_sq_le_energy (d : SourceData μ)
    (U : CanonicalMetricH1 d.potential) :
    ‖canonicalMetricValue d.potential U‖ ^ 2 ≤
      ∑ i : Fin n, ‖canonicalMetricGradient d.potential i U‖ ^ 2 := by
  have hclosed : IsClosed {W : WeightedEnergyAmbient d.potential |
      ‖W 0‖ ^ 2 ≤ ∑ i : Fin n, ‖W i.succ‖ ^ 2} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hcore : smoothCanonicalMetricGraphSet d.potential ⊆ {W : WeightedEnergyAmbient d.potential |
      ‖W 0‖ ^ 2 ≤ ∑ i : Fin n, ‖W i.succ‖ ^ 2} :=
    fun _ hW => source_core_value_norm_sq_le d hW
  have hU : (U : WeightedEnergyAmbient d.potential) ∈
      closure (smoothCanonicalMetricGraphSet d.potential) := by
    rw [← canonicalMetricGraph_coe_eq_closure d.source_C1.continuous]
    exact U.property
  exact (closure_minimal hcore hclosed) hU

theorem sourceMetricEnergy_isCoercive (d : SourceData μ) :
    IsCoercive (canonicalMetricEnergy d.potential) := by
  refine ⟨(1 / 2 : ℝ), by norm_num, fun U => ?_⟩
  have hp := sourceMetricValue_norm_sq_le_energy d U
  have hn := canonicalMetricH1_norm_sq d.potential U
  rw [canonicalMetricEnergy_self]
  nlinarith

/-- Constructed from the original target's actual source, not from an
assumed solution or classical source-regularity package. -/
def sourceMetricInverseH1 (d : SourceData μ) :
    Lp ℝ 2 (potentialMeasure d.potential) →L[ℝ] CanonicalMetricH1 d.potential :=
  (sourceMetricEnergy_isCoercive d).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (canonicalMetricValue d.potential).adjoint

def sourceMetricInverse (d : SourceData μ) :
    Lp ℝ 2 (potentialMeasure d.potential) →L[ℝ] Lp ℝ 2 (potentialMeasure d.potential) :=
  (canonicalMetricValue d.potential).comp (sourceMetricInverseH1 d)

theorem sourceMetricInverse_variational (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (V : CanonicalMetricH1 d.potential) :
    canonicalMetricEnergy d.potential (sourceMetricInverseH1 d g) V =
      inner ℝ g (canonicalMetricValue d.potential V) := by
  let hc := sourceMetricEnergy_isCoercive d
  rw [← hc.continuousLinearEquivOfBilin_apply]
  change inner ℝ (hc.continuousLinearEquivOfBilin
    (hc.continuousLinearEquivOfBilin.symm ((canonicalMetricValue d.potential).adjoint g))) V = _
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.adjoint_inner_left]

theorem sourceMetricInverse_unique (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) {U : CanonicalMetricH1 d.potential}
    (hU : ∀ V, canonicalMetricEnergy d.potential U V =
      inner ℝ g (canonicalMetricValue d.potential V)) : U = sourceMetricInverseH1 d g := by
  let hc := sourceMetricEnergy_isCoercive d
  have he : (canonicalMetricValue d.potential).adjoint g = hc.continuousLinearEquivOfBilin U := by
    apply hc.unique_continuousLinearEquivOfBilin
    intro V
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact (hU V).symm
  calc
    U = hc.continuousLinearEquivOfBilin.symm (hc.continuousLinearEquivOfBilin U) :=
      (hc.continuousLinearEquivOfBilin.symm_apply_apply U).symm
    _ = hc.continuousLinearEquivOfBilin.symm ((canonicalMetricValue d.potential).adjoint g) := by rw [he]
    _ = sourceMetricInverseH1 d g := rfl

theorem existsUnique_sourceMetricInverse (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    ∃! U : CanonicalMetricH1 d.potential, ∀ V,
      canonicalMetricEnergy d.potential U V = inner ℝ g (canonicalMetricValue d.potential V) :=
  ⟨sourceMetricInverseH1 d g, sourceMetricInverse_variational d g,
    fun _ hU => sourceMetricInverse_unique d g hU⟩

theorem sourceMetricInverse_energy_identity (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    (∑ i, ‖canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g)‖ ^ 2) =
      inner ℝ g (sourceMetricInverse d g) := by
  rw [← canonicalMetricEnergy_self]
  exact sourceMetricInverse_variational d g _

theorem sourceMetricInverse_norm_le (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) : ‖sourceMetricInverse d g‖ ≤ ‖g‖ := by
  let U := sourceMetricInverseH1 d g
  have hp := sourceMetricValue_norm_sq_le_energy d U
  have he := sourceMetricInverse_energy_identity d g
  change (∑ i, ‖canonicalMetricGradient d.potential i U‖ ^ 2) =
    inner ℝ g (canonicalMetricValue d.potential U) at he
  rw [he] at hp
  have hi := real_inner_le_norm g (canonicalMetricValue d.potential U)
  change ‖canonicalMetricValue d.potential U‖ ≤ ‖g‖
  by_cases hz : ‖canonicalMetricValue d.potential U‖ = 0
  · rw [hz]
    exact norm_nonneg _
  · have hn := lt_of_le_of_ne (norm_nonneg (canonicalMetricValue d.potential U)) (Ne.symm hz)
    nlinarith

theorem sourceMetricInverse_symmetric (d : SourceData μ)
    (f g : Lp ℝ 2 (potentialMeasure d.potential)) :
    inner ℝ (sourceMetricInverse d f) g = inner ℝ f (sourceMetricInverse d g) := by
  have hf := sourceMetricInverse_variational d f (sourceMetricInverseH1 d g)
  have hg := sourceMetricInverse_variational d g (sourceMetricInverseH1 d f)
  rw [canonicalMetricEnergy_symm] at hg
  rw [real_inner_comm g (sourceMetricInverse d f)]
  exact hg.symm.trans hf

theorem sourceMetricInverse_integral_eq_zero (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    (∫ x, sourceMetricInverse d g x ∂potentialMeasure d.potential) = 0 := by
  letI := d.source_probability
  exact canonicalMetricValue_integral_eq_zero d.source_C1.continuous _

/-- Actual compact variational Poisson equation, on the actual weak
canonical source constructed from the target. -/
theorem sourceMetricInverse_compact_test (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    (∑ i : Fin n, ∫ x,
      canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g) x *
        canonicalMetricDerivative d.potential ψ i x ∂potentialMeasure d.potential) =
      ∫ x, g x * (ψ x - ∫ y, ψ y ∂potentialMeasure d.potential)
        ∂potentialMeasure d.potential := by
  obtain ⟨V, hv, hd⟩ := exists_sourceMetricH1_of_smoothCompact d hψ hc
  have he := sourceMetricInverse_variational d g V
  rw [canonicalMetricEnergy_apply] at he
  have hl (i : Fin n) : inner ℝ
      (canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g))
      (canonicalMetricGradient d.potential i V) =
      ∫ x, canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g) x *
        canonicalMetricDerivative d.potential ψ i x ∂potentialMeasure d.potential := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hd i] with x hx
    simp only [hx, RCLike.inner_apply, conj_trivial, mul_comm]
  have hr : inner ℝ g (canonicalMetricValue d.potential V) =
      ∫ x, g x * (ψ x - ∫ y, ψ y ∂potentialMeasure d.potential)
        ∂potentialMeasure d.potential := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    simp only [hx, RCLike.inner_apply, conj_trivial, mul_comm]
  simp_rw [hl, hr] at he
  exact he

/-- Every bounded strongly convex admissible target law has an actually
constructed coercive canonical metric graph. -/
theorem exists_actual_coercive_source {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (hreg : HasSmoothBoundedStronglyConvexDensity μ) :
    ∃ d : SourceData μ, IsCoercive (canonicalMetricEnergy d.potential) := by
  obtain ⟨d⟩ := exists_sourceData hμ hreg
  exact ⟨d, sourceMetricEnergy_isCoercive d⟩

end KLSConstantImprovement.ActualWeakCanonicalMetricInverse
end

#print axioms KLSConstantImprovement.ActualWeakCanonicalMetricInverse.sourceMetricEnergy_isCoercive
#print axioms KLSConstantImprovement.ActualWeakCanonicalMetricInverse.existsUnique_sourceMetricInverse
#print axioms KLSConstantImprovement.ActualWeakCanonicalMetricInverse.sourceMetricInverse_compact_test
#print axioms KLSConstantImprovement.ActualWeakCanonicalMetricInverse.exists_actual_coercive_source

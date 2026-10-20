import KLSConstantImprovement.ActualBoundedCanonicalSource
import KLSConstantImprovement.ActualCanonicalMetricEnergyGraph
import KLS.WeakMomentLocalEssentialBounds
import KLS.WeakMomentRawTraceLocalIntegrability
import KLS.WeakHessianVariance

/-!
The constructed C1,1 canonical source supports the actual compact metric
core. Measurability, finite inverse-Hessian energy, and scalar BL are proved
from the actual weak source; no C4, pointwise SPD, or free BL premise is used.
The natural response/production graph closure is a separate obligation.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped BigOperators ContDiff Topology NNReal ENNReal MatrixOrder Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualWeakCanonicalMetricCore
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

/-- The positive definite cone is Borel, including in the entrywise topology. -/
theorem measurableSet_posDef :
    MeasurableSet {A : Matrix (Fin n) (Fin n) ℝ | A.PosDef} := by
  have he : {A : Matrix (Fin n) (Fin n) ℝ | A.PosDef} =
      {A | A.PosSemidef} ∩ {A | A.det ≠ 0} := by
    ext A
    constructor
    · intro hA
      exact ⟨hA.posSemidef, hA.det_pos.ne'⟩
    · rintro ⟨hA, hdet⟩
      exact hA.posDef_iff_det_ne_zero.mpr hdet
  rw [he]
  exact Matrix.posSemidef_is_closed.measurableSet.inter
    ((isClosed_eq (by fun_prop : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A.det))
      continuous_const).measurableSet.compl)

/-- The actual inverse positive root is AE strongly measurable whenever the
input is measurable and SPD AE. Its unspecified values away from that full
measure set cause no measurability assumption. -/
theorem inverseSqrtMatrix_aestronglyMeasurable_of_ae_posDef
    {α : Type*} [MeasurableSpace α] {ρ : Measure α}
    {H : α → Matrix (Fin n) (Fin n) ℝ} (hH : Measurable H)
    (hpos : ∀ᵐ x ∂ρ, (H x).PosDef) :
    AEStronglyMeasurable (fun x => inverseSqrtMatrix (H x)) ρ := by
  classical
  let S : Set (Matrix (Fin n) (Fin n) ℝ) := {A | A.PosDef}
  have hroot : ContinuousOn inverseSqrtMatrix S :=
    locallyLipschitzOn_inverseSqrtMatrix_posDef.continuousOn
  have hm : Measurable (S.piecewise inverseSqrtMatrix (fun _ => 0)) :=
    hroot.measurable_piecewise continuous_const.continuousOn measurableSet_posDef
  apply (hm.comp hH).aestronglyMeasurable.congr
  filter_upwards [hpos] with x hx
  exact S.piecewise_eq_of_mem _ _ hx

/-- The actual source inverse Hessian is locally integrable; the bound comes
from its AE MA equation and the positive continuous density on compacts. -/
theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.inverseHessian_locallyIntegrable {μ : Measure (Space n)}
    (d : SourceData μ) (i j : Fin n) :
    LocallyIntegrable (fun x => (coordinateHessian d.potential x)⁻¹ i j) volume := by
  apply locallyIntegrable_of_memLp_two_on_compacts
  intro E hE
  letI : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hE.measure_ne_top
  exact (memLp_inverseHessian_top_on_compact_of_ae_equation
    d.source_lipschitz d.gradient_lipschitz d.target_smooth.continuous
    (d.hessian_ae.mono fun _ hx => ⟨hx.1, hx.2.1⟩) hE i j).mono_exponent (by simp)

/-- Compact C1 tests have actual finite inverse-Hessian energy on the
constructed source, with all coefficient/weight integrability discharged. -/
theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.compact_inverse_energy_integrable {μ : Measure (Space n)}
    (d : SourceData μ) {f : Space n → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    Integrable (inverseHessianGradientForm d.potential f) (potentialMeasure d.potential) := by
  unfold inverseHessianGradientForm
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  have hdi := (contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous
  have hdj := (contDiff_coordinateDerivative hf (m := 0) (by norm_num) j).continuous
  have hi := integrable_compact_mul_potential_of_locallyIntegrable
    d.source_C1.continuous (d.inverseHessian_locallyIntegrable i j) (hdi.mul hdj)
    ((hasCompactSupport_coordinateDerivative hc i).mul_right)
  simpa only [Pi.mul_apply, mul_comm, mul_left_comm, mul_assoc] using hi

/-- Scalar Brascamp--Lieb on the actual canonical source at compact C1 tests.
The ordinary source diffusion range is discharged by the accepted C1 weak
theorem; no canonical-metric strong-operator core is inferred. -/
theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.compact_brascampLieb {μ : Measure (Space n)}
    (d : SourceData μ) {f : Space n → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    ProbabilityTheory.variance f (potentialMeasure d.potential) ≤
      ∫ x, inverseHessianGradientForm d.potential f x ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  exact brascampLieb_variance_raw_weak_C11 d.source_C1 d.gradient_lipschitz.locallyLipschitz
    (d.hessian_ae.mono fun _ hx => hx.1)
    (memLp_of_continuous_hasCompactSupport d.source_C1.continuous hf.continuous hc)
    (fun i => (contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous.locallyIntegrable)
    (fun i => hasLocalWeakCoordinateDerivative_of_locallyLipschitz hf.locallyLipschitz i)
    (d.compact_inverse_energy_integrable hf hc)

/-- The actual root-gradient coordinates are AE strongly measurable in the
constructed source law, despite the Hessian only being defined weakly AE. -/
theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.metric_derivative_aestronglyMeasurable {μ : Measure (Space n)}
    (d : SourceData μ) {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin n) :
    AEStronglyMeasurable (canonicalMetricDerivative d.potential f i)
      (potentialMeasure d.potential) := by
  have hroot := inverseSqrtMatrix_aestronglyMeasurable_of_ae_posDef
    (measurable_coordinateHessian d.potential) (d.hessian_ae_source.mono fun _ hx => hx.1)
  unfold canonicalMetricDerivative canonicalMetricRoot
  exact Finset.univ.aestronglyMeasurable_fun_sum fun j _ =>
    ((continuous_apply j).comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable hroot)).mul
      (contDiff_coordinateDerivative hf (m := 0) (by norm_num) j).continuous.aestronglyMeasurable

/-- Pointwise root factorization only needs SPD at the point being used. -/
theorem canonicalMetricRoot_gram_at {φ : Space n → ℝ} {x : Space n}
    (hpos : (coordinateHessian φ x).PosDef) :
    (canonicalMetricRoot φ x).transpose * canonicalMetricRoot φ x =
      (coordinateHessian φ x)⁻¹ := by
  unfold canonicalMetricRoot
  rw [(inverseSqrtMatrix_isSymm (coordinateHessian φ x)).eq]
  unfold inverseSqrtMatrix
  rw [← Matrix.mul_inv_rev,
    CFC.sqrt_mul_sqrt_self (coordinateHessian φ x) hpos.posSemidef.nonneg]

/-- The actual metric-gradient square identity holds at every AE SPD point. -/
theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.metric_derivative_sq_ae {μ : Measure (Space n)} (d : SourceData μ)
    (f : Space n → ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      (∑ i, canonicalMetricDerivative d.potential f i x ^ 2) =
        inverseHessianGradientForm d.potential f x := by
  filter_upwards [d.hessian_ae_source] with x hx
  let R := canonicalMetricRoot d.potential x
  let a : Fin n → ℝ := fun i => coordinateDerivative f i x
  have he : (R *ᵥ a) ⬝ᵥ (R *ᵥ a) =
      a ⬝ᵥ ((coordinateHessian d.potential x)⁻¹ *ᵥ a) := by
    rw [← Matrix.dotProduct_transpose_mulVec R a (R *ᵥ a),
      Matrix.mulVec_mulVec, canonicalMetricRoot_gram_at hx.1]
  change (∑ i, (R *ᵥ a) i ^ 2) = _
  calc
    _ = (R *ᵥ a) ⬝ᵥ (R *ᵥ a) := by simp only [dotProduct, pow_two]
    _ = _ := he
    _ = _ := (matrix_quadratic_sum_eq_dotProduct (coordinateHessian d.potential x)⁻¹ a).symm

/-- Compact C1 tests belong to the actual canonical metric-gradient L2
space. This is the missing weak-source compact-core input for the metric
form construction; it asserts no strong graph-core or response identity. -/
theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.metric_derivative_memLp {μ : Measure (Space n)}
    (d : SourceData μ) {f : Space n → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (i : Fin n) :
    MemLp (canonicalMetricDerivative d.potential f i) 2 (potentialMeasure d.potential) := by
  have hm := d.metric_derivative_aestronglyMeasurable hf i
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply (d.compact_inverse_energy_integrable hf hc).mono' (hm.pow 2)
  filter_upwards [d.metric_derivative_sq_ae f] with x hx
  change ‖canonicalMetricDerivative d.potential f i x ^ 2‖ ≤
    inverseHessianGradientForm d.potential f x
  rw [Real.norm_of_nonneg (sq_nonneg _), ← hx]
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin n => (canonicalMetricDerivative d.potential f j x) ^ 2)
    (fun j _ => sq_nonneg (canonicalMetricDerivative d.potential f j x)) (Finset.mem_univ i)

end KLSConstantImprovement.ActualWeakCanonicalMetricCore
#print axioms KLSConstantImprovement.ActualWeakCanonicalMetricCore.measurableSet_posDef
#print axioms KLSConstantImprovement.ActualWeakCanonicalMetricCore.inverseSqrtMatrix_aestronglyMeasurable_of_ae_posDef
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.inverseHessian_locallyIntegrable
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.compact_inverse_energy_integrable
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.compact_brascampLieb
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.metric_derivative_aestronglyMeasurable
#print axioms KLSConstantImprovement.ActualWeakCanonicalMetricCore.canonicalMetricRoot_gram_at
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.metric_derivative_sq_ae
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.metric_derivative_memLp

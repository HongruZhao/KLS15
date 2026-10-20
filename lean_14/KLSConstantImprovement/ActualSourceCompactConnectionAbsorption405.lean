import KLSConstantImprovement.ActualSourceCompactConnectionBalance405
import KLSConstantImprovement.ActualSourceConnectionPointwise405

/-! Positive compact absorption on the actual source. This uses the actual
weak Hessian balance after all product domains are paid. Bounded mass is
explicit and only supplies the true cutoff error M*Gamma(chi). -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff NNReal ENNReal
namespace KLSConstantImprovement.ActualSourceCompactConnectionAbsorption405
open KLS ActualBoundedCanonicalSource ActualSourceHessianEvolution405 ActualSourceConnectionFields405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405 ActualSourceBoundedMassCutoffs405
open ActualSourceCompactConnectionDomains405 ActualSourceCompactConnectionBalance405 ActualSourceConnectionPointwise405
open ActualCompatibleJacobianCoercivity405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem sourceVectorMass_nonnegative_ae (d : SourceData μ) (u : Fin n → Space n → ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential, 0 ≤ sourceVectorMass d.potential u x := by
  filter_upwards [d.hessian_ae_source] with x hx
  rw [sourceVectorMass, matrix_quadratic_sum_eq_dotProduct]
  exact hx.1.posSemidef.dotProduct_mulVec_nonneg _

theorem sourceVectorJacobianEnergy_nonnegative_ae (d : SourceData μ)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hc : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i j => Du i j x)).IsSymm) :
    ∀ᵐ x ∂potentialMeasure d.potential, 0 ≤ sourceVectorJacobianEnergy Du x := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source, hc.filter_mono hac.ae_le] with x hp hD
  have he := compatible_jacobian_trace_nonneg (coordinateHessian d.potential x)
    (Matrix.of (fun i j => Du i j x)) hp.1 hD
  simpa only [sourceVectorJacobianEnergy, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.of_apply] using he

theorem compact_mass_weighted_cutoff_integrable (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d g) x ≤ C)
    (hMi : Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g)) (potentialMeasure d.potential))
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) :
    Integrable (fun x => sourceVectorMass d.potential (naturalCanonicalFlux d g) x *
      inverseHessianGradientForm d.potential χ x) (potentialMeasure d.potential) := by
  apply (d.compact_inverse_energy_integrable hχ hc).bdd_mul hMi.aestronglyMeasurable
  filter_upwards [sourceVectorMass_nonnegative_ae d (naturalCanonicalFlux d g), hM] with x hp hb
  rwa [Real.norm_of_nonneg hp]

/-- The constant in this absorption is temporary. The exact connection
balance is retained for the later radius limit, so no constant is lost in
the final canonical Bochner completion. -/
theorem integral_actual_compact_connection_absorption (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d g) x ≤ C)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i a E, IsCompact E → MemLp (Du i a) 2 (volume.restrict E))
    (hw : ∀ i a, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i a) a)
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i j => Du i j x)).IsSymm)
    (hMi : Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g)) (potentialMeasure d.potential))
    (hQi : Integrable (sourceVectorJacobianEnergy Du) (potentialMeasure d.potential))
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) :
    (∫ x, χ x ^ 2 * sourceConnectionGamma d (naturalCanonicalFlux d g) x ∂potentialMeasure d.potential) ≤
      2 * (∫ x, χ x ^ 2 * sourceVectorMass d.potential (naturalCanonicalFlux d g) x ∂potentialMeasure d.potential) +
      8 * (∫ x, χ x ^ 2 * sourceVectorJacobianEnergy Du x ∂potentialMeasure d.potential) +
      8 * (∫ x, sourceVectorMass d.potential (naturalCanonicalFlux d g) x *
        inverseHessianGradientForm d.potential χ x ∂potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let u := naturalCanonicalFlux d g
  obtain ⟨hX, hB, hH, hP, hG⟩ := compact_connection_fields_integrable d g hC hM Du hu hDu hw hχ hc
  change Integrable (fun x => χ x ^ 2 * sourceConnectionCross d u Du x) (potentialMeasure d.potential) at hX
  change Integrable (fun x => χ x * sourceConnectionBoundary d χ u x) (potentialMeasure d.potential) at hB
  change Integrable (fun x => χ x ^ 2 * sourceVectorMass d.potential u x) (potentialMeasure d.potential) at hH
  change Integrable (fun x => χ x ^ 2 * sourceConnectionTarget d u x) (potentialMeasure d.potential) at hP
  change Integrable (fun x => χ x ^ 2 * sourceConnectionGamma d u x) (potentialMeasure d.potential) at hG
  have hχtop : MemLp (fun x => χ x ^ 2) ∞ (potentialMeasure d.potential) :=
    (hχ.pow 2).continuous.memLp_of_hasCompactSupport (by
      simpa only [pow_two, Pi.mul_def] using hc.mul_right (f' := χ))
  have hQ : Integrable (fun x => χ x ^ 2 * sourceVectorJacobianEnergy Du x) (potentialMeasure d.potential) :=
    hQi.mul_of_top_right hχtop
  have hE : Integrable (fun x => sourceVectorMass d.potential u x *
      inverseHessianGradientForm d.potential χ x) (potentialMeasure d.potential) :=
    compact_mass_weighted_cutoff_integrable d g hC hM hMi hχ hc
  have hleft : Integrable (fun x => -(χ x ^ 2 * sourceConnectionCross d u Du x) -
      2 * (χ x * sourceConnectionBoundary d χ u x)) (potentialMeasure d.potential) :=
    hX.neg.sub (hB.const_mul 2)
  have hright : Integrable (fun x => (1/2 : ℝ) * (χ x ^ 2 * sourceConnectionGamma d u x) +
      4 * (χ x ^ 2 * sourceVectorJacobianEnergy Du x) +
      4 * (sourceVectorMass d.potential u x * inverseHessianGradientForm d.potential χ x))
      (potentialMeasure d.potential) := ((hG.const_mul (1/2)).add (hQ.const_mul 4)).add (hE.const_mul 4)
  have hpoint : ∀ᵐ x ∂potentialMeasure d.potential,
      -(χ x ^ 2 * sourceConnectionCross d u Du x) - 2 * (χ x * sourceConnectionBoundary d χ u x) ≤
        (1/2 : ℝ) * (χ x ^ 2 * sourceConnectionGamma d u x) +
        4 * (χ x ^ 2 * sourceVectorJacobianEnergy Du x) +
        4 * (sourceVectorMass d.potential u x * inverseHessianGradientForm d.potential χ x) := by
    filter_upwards [sourceConnectionCross_abs_le_ae d u Du hcomp,
      sourceConnectionBoundary_abs_le_ae d u χ] with x hcross hbound
    have hx := mul_le_mul_of_nonneg_left ((neg_le_abs (sourceConnectionCross d u Du x)).trans hcross)
      (sq_nonneg (χ x))
    have hb := (neg_le_abs (2 * (χ x * sourceConnectionBoundary d χ u x))).trans hbound
    nlinarith
  have hint := integral_mono_ae hleft hright hpoint
  have hPnonneg : 0 ≤ ∫ x, χ x ^ 2 * sourceConnectionTarget d u x ∂potentialMeasure d.potential :=
    integral_nonneg_of_ae (by
      filter_upwards [sourceConnectionTarget_nonnegative_ae d u] with x hx
      exact mul_nonneg (sq_nonneg (χ x)) hx)
  have hbalance := integral_actual_compact_connection_balance d g hC hM Du hu hDu hw hχ hc
  have hPG : (∫ x, χ x ^ 2 * (sourceConnectionTarget d u x + sourceConnectionGamma d u x)
      ∂potentialMeasure d.potential) =
      (∫ x, χ x ^ 2 * sourceConnectionTarget d u x ∂potentialMeasure d.potential) +
        ∫ x, χ x ^ 2 * sourceConnectionGamma d u x ∂potentialMeasure d.potential := by
    simp only [mul_add]
    exact integral_add hP hG
  have hli : (∫ x, -(χ x ^ 2 * sourceConnectionCross d u Du x) -
      2 * (χ x * sourceConnectionBoundary d χ u x) ∂potentialMeasure d.potential) =
      -(∫ x, χ x ^ 2 * sourceConnectionCross d u Du x ∂potentialMeasure d.potential) -
        2 * (∫ x, χ x * sourceConnectionBoundary d χ u x ∂potentialMeasure d.potential) := by
    have hnx : Integrable (fun x => -(χ x ^ 2 * sourceConnectionCross d u Du x))
        (potentialMeasure d.potential) := hX.neg
    have h2b : Integrable (fun x => 2 * (χ x * sourceConnectionBoundary d χ u x))
        (potentialMeasure d.potential) := hB.const_mul 2
    rw [integral_sub hnx h2b, integral_neg, integral_const_mul]
  have hri : (∫ x, (1/2 : ℝ) * (χ x ^ 2 * sourceConnectionGamma d u x) +
      4 * (χ x ^ 2 * sourceVectorJacobianEnergy Du x) +
      4 * (sourceVectorMass d.potential u x * inverseHessianGradientForm d.potential χ x)
      ∂potentialMeasure d.potential) =
      (1/2 : ℝ) * (∫ x, χ x ^ 2 * sourceConnectionGamma d u x ∂potentialMeasure d.potential) +
      4 * (∫ x, χ x ^ 2 * sourceVectorJacobianEnergy Du x ∂potentialMeasure d.potential) +
      4 * (∫ x, sourceVectorMass d.potential u x * inverseHessianGradientForm d.potential χ x
        ∂potentialMeasure d.potential) := by
    have hhalf : Integrable (fun x => (1/2 : ℝ) * (χ x ^ 2 * sourceConnectionGamma d u x))
        (potentialMeasure d.potential) := hG.const_mul (1/2)
    have h4q : Integrable (fun x => 4 * (χ x ^ 2 * sourceVectorJacobianEnergy Du x))
        (potentialMeasure d.potential) := hQ.const_mul 4
    have h4e : Integrable (fun x => 4 * (sourceVectorMass d.potential u x * inverseHessianGradientForm d.potential χ x))
        (potentialMeasure d.potential) := hE.const_mul 4
    have hsum : Integrable (fun x => (1/2 : ℝ) * (χ x ^ 2 * sourceConnectionGamma d u x) +
        4 * (χ x ^ 2 * sourceVectorJacobianEnergy Du x)) (potentialMeasure d.potential) := hhalf.add h4q
    rw [integral_add hsum h4e, integral_add hhalf h4q]
    simp only [integral_const_mul]
  rw [hPG] at hbalance
  rw [hli, hri] at hint
  linarith

end KLSConstantImprovement.ActualSourceCompactConnectionAbsorption405
#print axioms KLSConstantImprovement.ActualSourceCompactConnectionAbsorption405.sourceVectorMass_nonnegative_ae
#print axioms KLSConstantImprovement.ActualSourceCompactConnectionAbsorption405.sourceVectorJacobianEnergy_nonnegative_ae
#print axioms KLSConstantImprovement.ActualSourceCompactConnectionAbsorption405.compact_mass_weighted_cutoff_integrable
#print axioms KLSConstantImprovement.ActualSourceCompactConnectionAbsorption405.integral_actual_compact_connection_absorption

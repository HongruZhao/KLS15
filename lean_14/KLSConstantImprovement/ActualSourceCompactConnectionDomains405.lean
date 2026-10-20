import KLSConstantImprovement.ActualSourceConnectionFields405
import KLSConstantImprovement.ActualSourceBoundedMassConnectionTests405
import KLS.WeakHessianInverseDerivative

/-! Actual compact connection domains. A bounded natural mass is still an
explicit premise. It pays local bounded vector products; the actual weak
Monge--Ampere equation pays the inverse coefficient, and the proved raw
Hessian equation then pays every signed compact connection product. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff NNReal ENNReal
namespace KLSConstantImprovement.ActualSourceCompactConnectionDomains405
open KLS ActualBoundedCanonicalSource ActualBoundedRawMetricDomain
open ActualSourceHessianEvolution405 ActualSourceCurvatureDomains405 ActualSourceConnectionFields405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405 ActualSourceBoundedMassCutoffs405
open ActualSourceBoundedMassConnectionTests405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem memLp_top_of_absoluteContinuity {ρ ν : Measure (Space n)} (ha : ρ ≪ ν)
    {f : Space n → ℝ} (hf : MemLp f ∞ ν) : MemLp f ∞ ρ := by
  have he : eLpNormEssSup f ν < ⊤ := eLpNormEssSup_le_eLpNorm_top.trans_lt hf.eLpNorm_lt_top
  obtain ⟨B, hB⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp he
  apply memLp_top_of_bound (hf.aestronglyMeasurable.mono_ac ha) (B : ℝ)
  filter_upwards [hB.filter_mono ha.ae_le] with x hx
  exact_mod_cast hx

theorem actual_connection_flux_local_L2 (d : SourceData μ) (i a j : Fin n)
    (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (fun x => ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j)
      2 (volume.restrict E) := by
  obtain ⟨hJ, _, _⟩ := actual_mongeAmpere_inverse_hasLocalWeakDerivative
    (T := sourceThirdMatrix d) d.source_C1 (d.target_smooth.of_le (by simp))
    d.gradient_lipschitz (d.hessian_ae.mono fun _ hx => hx.2.1)
    d.third_local_L2 d.third_weak_derivative
  have hs : MemLp (fun x => ∑ b : Fin n,
      (coordinateHessian d.potential x)⁻¹ a b * sourceThirdMatrix d x i b j) 2
      (volume.restrict E) :=
    memLp_finsetSum Finset.univ fun b _ => (hJ a b E hE).mul (d.third_local_L2 i b j E hE)
  simpa only [Matrix.mul_apply] using hs

theorem coordinateDerivative_square {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ)
    (a : Fin n) (x : Space n) :
    coordinateDerivative (fun y => χ y ^ 2) a x = 2 * χ x * coordinateDerivative χ a x := by
  have he : (fun y => χ y ^ 2) = (fun y => χ y * χ y) := by funext y; ring
  rw [he, coordinateDerivative_mul (hχ.differentiable (by norm_num) x)
    (hχ.differentiable (by norm_num) x)]
  ring

theorem compact_connection_boundary_summand_memLp (d : SourceData μ)
    {u : Fin n → Space n → ℝ}
    (hu : ∀ i E, IsCompact E → MemLp (u i) ∞ (volume.restrict E))
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (i j a : Fin n) :
    MemLp (fun x => χ x *
      (((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
        (u i x * u j x) * coordinateDerivative χ a x)) 2 (potentialMeasure d.potential) := by
  have hloc (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
        (u i x * u j x) * coordinateDerivative χ a x) 2 (volume.restrict E) := by
    have huu : MemLp (fun x => u i x * u j x) ∞ (volume.restrict E) :=
      (hu i E hE).mul (hu j E hE)
    have hp : MemLp (fun x => ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
        (u i x * u j x)) 2 (volume.restrict E) :=
      (actual_connection_flux_local_L2 d i a j E hE).mul huu
    have hm := memLp_continuous_mul_on_compact hE hp
      (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) a).continuous
    apply (memLp_congr_ae (Eventually.of_forall fun x => ?_)).mp hm
    exact mul_comm _ _
  have hv := memLp_compact_mul_of_local hχ.continuous hc hloc
  exact memLp_potentialMeasure_of_compact_localL2 d.source_C1.continuous hc.mul_right
    (fun E _ => hv.restrict E)

/-- Every entry of the signed compact connection expansion has an actual
L1 domain before any cancellation or finite sum is performed. -/
theorem compact_connection_summands_integrable (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d g) x ≤ C)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i a E, IsCompact E → MemLp (Du i a) 2 (volume.restrict E))
    (hw : ∀ i a, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i a) a)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) :
    (∀ i j a, Integrable (fun x => χ x ^ 2 *
      (((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
        (Du i a x * naturalCanonicalFlux d g j x + naturalCanonicalFlux d g i x * Du j a x)))
      (potentialMeasure d.potential)) ∧
    (∀ i j a, Integrable (fun x => χ x *
      (((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
        (naturalCanonicalFlux d g i x * naturalCanonicalFlux d g j x) * coordinateDerivative χ a x))
      (potentialMeasure d.potential)) ∧
    (∀ i j, Integrable (fun x => χ x ^ 2 * coordinateHessian d.potential x i j *
      naturalCanonicalFlux d g i x * naturalCanonicalFlux d g j x) (potentialMeasure d.potential)) ∧
    (∀ i j, Integrable (fun x => χ x ^ 2 * sourceTargetCurvature d x i j *
      naturalCanonicalFlux d g i x * naturalCanonicalFlux d g j x) (potentialMeasure d.potential)) ∧
    (∀ i j, Integrable (fun x => χ x ^ 2 *
      matrixTraceGram (coordinateHessian d.potential x)⁻¹ (sourceThirdMatrix d x) i j *
        naturalCanonicalFlux d g i x * naturalCanonicalFlux d g j x) (potentialMeasure d.potential)) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let u := naturalCanonicalFlux d g
  have huTop (i : Fin n) (E : Set (Space n)) (hE : IsCompact E) : MemLp (u i) ∞ (volume.restrict E) :=
    naturalCanonicalFlux_local_top_of_mass_bound d g hC hM i hE
  have htest (i j : Fin n) : MemLp (boundedMassQuadraticTest χ u i j) ∞
      (potentialMeasure d.potential) :=
    memLp_top_of_absoluteContinuity (withDensity_absolutelyContinuous _ _)
      (boundedMassQuadraticTest_memLp_top hχ hc huTop i j)
  have hB (i j a : Fin n) : Integrable (fun x => χ x *
      (((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
        (u i x * u j x) * coordinateDerivative χ a x)) (potentialMeasure d.potential) :=
    (compact_connection_boundary_summand_memLp d huTop hχ hc i j a).integrable (by norm_num)
  refine ⟨?_, hB, ?_, ?_, ?_⟩
  · intro i j a
    have ht := (actual_boundedMass_compact_quadratic_hessian_evolution d g hC hM Du hu hDu hw hχ hc i j).1 a
    apply (ht.sub ((hB i j a).const_mul 2)).congr
    exact Eventually.of_forall fun x => by
      dsimp only [Pi.sub_apply, Pi.mul_apply, boundedMassQuadraticDerivative, rawCutoffDerivative, u]
      rw [coordinateDerivative_square hχ]
      ring
  · intro i j
    have ht := ((d.hessian_entry_memLp i j 1).integrable le_rfl).mul_of_top_left (htest i j)
    apply ht.congr
    exact Eventually.of_forall fun x => by
      dsimp only [Pi.mul_apply, boundedMassQuadraticTest]
      ring
  · intro i j
    have ht := ((actual_target_curvature_entry_memLp_top d i j).integrable (by norm_num)).mul_of_top_left (htest i j)
    apply ht.congr
    exact Eventually.of_forall fun x => by
      dsimp only [Pi.mul_apply, boundedMassQuadraticTest]
      ring
  · intro i j
    have ht := (actual_third_gram_entry_integrable d i j).mul_of_top_left (htest i j)
    apply ht.congr
    exact Eventually.of_forall fun x => by
      dsimp only [Pi.mul_apply, boundedMassQuadraticTest]
      ring

/-- Compact scalar fields are integrable as literal aggregate functions. -/
theorem compact_connection_fields_integrable (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d g) x ≤ C)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i a E, IsCompact E → MemLp (Du i a) 2 (volume.restrict E))
    (hw : ∀ i a, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i a) a)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) :
    Integrable (fun x => χ x ^ 2 * sourceConnectionCross d (naturalCanonicalFlux d g) Du x) (potentialMeasure d.potential) ∧
    Integrable (fun x => χ x * sourceConnectionBoundary d χ (naturalCanonicalFlux d g) x) (potentialMeasure d.potential) ∧
    Integrable (fun x => χ x ^ 2 * sourceVectorMass d.potential (naturalCanonicalFlux d g) x) (potentialMeasure d.potential) ∧
    Integrable (fun x => χ x ^ 2 * sourceConnectionTarget d (naturalCanonicalFlux d g) x) (potentialMeasure d.potential) ∧
    Integrable (fun x => χ x ^ 2 * sourceConnectionGamma d (naturalCanonicalFlux d g) x) (potentialMeasure d.potential) := by
  obtain ⟨hX, hB, hH, hP, hG⟩ := compact_connection_summands_integrable d g hC hM Du hu hDu hw hχ hc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [sourceConnectionCross, Finset.mul_sum] using
      integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ =>
        integrable_finsetSum Finset.univ (fun a _ => hX i j a)))
  · simpa only [sourceConnectionBoundary, Finset.mul_sum] using
      integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ =>
        integrable_finsetSum Finset.univ (fun a _ => hB i j a)))
  · simpa only [sourceVectorMass, Finset.mul_sum, mul_assoc] using
      integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hH i j))
  · simpa only [sourceConnectionTarget, Finset.mul_sum, mul_assoc] using
      integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hP i j))
  · simpa only [sourceConnectionGamma, Finset.mul_sum, mul_assoc] using
      integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hG i j))

end KLSConstantImprovement.ActualSourceCompactConnectionDomains405
#print axioms KLSConstantImprovement.ActualSourceCompactConnectionDomains405.memLp_top_of_absoluteContinuity
#print axioms KLSConstantImprovement.ActualSourceCompactConnectionDomains405.actual_connection_flux_local_L2
#print axioms KLSConstantImprovement.ActualSourceCompactConnectionDomains405.coordinateDerivative_square
#print axioms KLSConstantImprovement.ActualSourceCompactConnectionDomains405.compact_connection_boundary_summand_memLp
#print axioms KLSConstantImprovement.ActualSourceCompactConnectionDomains405.compact_connection_summands_integrable
#print axioms KLSConstantImprovement.ActualSourceCompactConnectionDomains405.compact_connection_fields_integrable

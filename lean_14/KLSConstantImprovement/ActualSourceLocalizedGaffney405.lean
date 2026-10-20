import KLSConstantImprovement.ActualSourceVectorCutoffDomains405
import KLSConstantImprovement.ActualVectorCutoffAlgebra405

/-!
The literal localized Gaffney balance on the actual source measure.
The raw Jacobian is only locally L2. All cutoff products are proved
integrable before the compact weak vector Bochner identity is expanded.
Both signed boundary terms are retained.
-/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceLocalizedGaffney405
open KLS ActualBoundedCanonicalSource ActualBoundedRawMetricDomain
open ActualSourceVectorCutoffDomains405 ActualVectorCutoffAlgebra405
open ActualCompactWeakSourceVectorSquare
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

def sourceVectorMass (φ : Space n → ℝ) (u : Fin n → Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, coordinateHessian φ x i j * u i x * u j x

def sourceVectorJacobianEnergy (Du : Fin n → Fin n → Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, Du i j x * Du j i x

def sourceVectorCutoffDot (χ : Space n → ℝ) (u : Fin n → Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i : Fin n, coordinateDerivative χ i x * u i x

def sourceVectorCutoffCross (χ : Space n → ℝ) (u : Fin n → Space n → ℝ)
    (Du : Fin n → Fin n → Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, coordinateDerivative χ j x * u i x * Du j i x

theorem source_vector_mass_integrable (d : SourceData μ)
    (u : Fin n → Space n → ℝ) (hu : ∀ i, MemLp (u i) 2 (potentialMeasure d.potential)) :
    Integrable (sourceVectorMass d.potential u) (potentialMeasure d.potential) := by
  apply integrable_finsetSum Finset.univ
  intro i _
  apply integrable_finsetSum Finset.univ
  intro j _
  have hm : MemLp (fun x => coordinateHessian d.potential x i j * u i x)
      2 (potentialMeasure d.potential) :=
    (memLp_coordinateHessian_top_of_gradient_lipschitz d.gradient_lipschitz
      (potentialMeasure d.potential) i j).mul (hu i)
  exact hm.integrable_mul (hu j)

/-- Compact Jacobian and cutoff-gradient products have their actual L2
domains without any global Jacobian energy premise. -/
theorem source_vector_cutoff_products_memLp (d : SourceData μ)
    (u : Fin n → Space n → ℝ) (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i, MemLp (u i) 2 (potentialMeasure d.potential))
    (hDu : ∀ i j E, IsCompact E → MemLp (Du i j) 2 (volume.restrict E))
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) :
    (∀ i j, MemLp (fun x => χ x * Du i j x) 2 (potentialMeasure d.potential)) ∧
      (∀ i j, MemLp (fun x => coordinateDerivative χ j x * u i x)
        2 (potentialMeasure d.potential)) ∧
      MemLp (sourceVectorCutoffDot χ u) 2 (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hχDu (i j : Fin n) : MemLp (fun x => χ x * Du i j x) 2 (potentialMeasure d.potential) := by
    have hvol : MemLp (fun x => χ x * Du i j x) 2 volume :=
      memLp_compact_mul_of_local hχ.continuous hc (hDu i j)
    exact memLp_potentialMeasure_of_compact_localL2 d.source_C1.continuous hc.mul_right
      (fun E _ => hvol.restrict E)
  have hDχu (i j : Fin n) : MemLp (fun x => coordinateDerivative χ j x * u i x)
      2 (potentialMeasure d.potential) := by
    have ht : MemLp (coordinateDerivative χ j) ∞ (potentialMeasure d.potential) :=
      (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) j).continuous.memLp_of_hasCompactSupport
        (hasCompactSupport_coordinateDerivative hc j)
    exact ht.mul (hu i)
  refine ⟨hχDu, hDχu, ?_⟩
  exact memLp_finsetSum Finset.univ (fun i _ => hDχu i i)

theorem source_vector_cutoff_energy_integrable (d : SourceData μ)
    (u : Fin n → Space n → ℝ) (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i, MemLp (u i) 2 (potentialMeasure d.potential))
    (hDu : ∀ i j E, IsCompact E → MemLp (Du i j) 2 (volume.restrict E))
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) :
    Integrable (fun x => χ x ^ 2 *
      (sourceVectorMass d.potential u x + sourceVectorJacobianEnergy Du x)) (potentialMeasure d.potential) ∧
      Integrable (fun x => χ x * sourceVectorCutoffCross χ u Du x) (potentialMeasure d.potential) ∧
      Integrable (fun x => sourceVectorCutoffDot χ u x ^ 2) (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  obtain ⟨hχDu, hDχu, hb⟩ := source_vector_cutoff_products_memLp d u Du hu hDu hχ hc
  have hχtop : MemLp χ ∞ (potentialMeasure d.potential) := hχ.continuous.memLp_of_hasCompactSupport hc
  have hM : Integrable (fun x => χ x ^ 2 * sourceVectorMass d.potential u x)
      (potentialMeasure d.potential) := by
    have hm := source_vector_mass_integrable d (fun i x => χ x * u i x)
      (fun i => hχtop.mul (hu i))
    apply hm.congr
    exact Eventually.of_forall fun x => by
      simp only [sourceVectorMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
  have hQ : Integrable (fun x => χ x ^ 2 * sourceVectorJacobianEnergy Du x)
      (potentialMeasure d.potential) := by
    have hm : Integrable (fun x => ∑ i : Fin n, ∑ j : Fin n,
        (χ x * Du i j x) * (χ x * Du j i x)) (potentialMeasure d.potential) :=
      integrable_finsetSum Finset.univ (fun i _ =>
        integrable_finsetSum Finset.univ (fun j _ => (hχDu i j).integrable_mul (hχDu j i)))
    apply hm.congr
    exact Eventually.of_forall fun x => by
      simp only [sourceVectorJacobianEnergy, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
  have hC : Integrable (fun x => χ x * sourceVectorCutoffCross χ u Du x)
      (potentialMeasure d.potential) := by
    have hm : Integrable (fun x => ∑ i : Fin n, ∑ j : Fin n,
        (coordinateDerivative χ j x * u i x) * (χ x * Du j i x)) (potentialMeasure d.potential) :=
      integrable_finsetSum Finset.univ (fun i _ =>
        integrable_finsetSum Finset.univ (fun j _ => (hDχu i j).integrable_mul (hχDu j i)))
    apply hm.congr
    exact Eventually.of_forall fun x => by
      simp only [sourceVectorCutoffCross, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
  refine ⟨?_, hC, ?_⟩
  · have hm := hM.add hQ
    apply hm.congr
    exact Eventually.of_forall fun x => by dsimp only [Pi.add_apply]; ring
  · have hm := hb.integrable_mul hb
    change Integrable (fun x => sourceVectorCutoffDot χ u x * sourceVectorCutoffDot χ u x)
      (potentialMeasure d.potential) at hm
    simpa only [pow_two] using hm

/-- Actual local energy identity, with both signed boundary terms. -/
theorem integral_source_vector_localized_gaffney (d : SourceData μ)
    (u : Fin n → Space n → ℝ) (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i, MemLp (u i) 2 (potentialMeasure d.potential))
    (hDu : ∀ i j E, IsCompact E → MemLp (Du i j) 2 (volume.restrict E))
    (hw : ∀ i j, HasLocalWeakCoordinateDerivative (u i) (Du i j) j)
    (g : Space n → ℝ) (hg : MemLp g 2 (potentialMeasure d.potential))
    (hadj : rawWeakSourceVectorAdjoint d.potential u Du =ᵐ[potentialMeasure d.potential] g)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) :
    (∫ x, χ x ^ 2 * (sourceVectorMass d.potential u x + sourceVectorJacobianEnergy Du x)
      ∂potentialMeasure d.potential) =
      (∫ x, χ x ^ 2 * g x ^ 2 ∂potentialMeasure d.potential) -
        2 * (∫ x, χ x * g x * sourceVectorCutoffDot χ u x ∂potentialMeasure d.potential) -
        2 * (∫ x, χ x * sourceVectorCutoffCross χ u Du x ∂potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  obtain ⟨hE, hC, hb2⟩ := source_vector_cutoff_energy_integrable d u Du hu hDu hχ hc
  have hb := (source_vector_cutoff_products_memLp d u Du hu hDu hχ hc).2.2
  have hχtop : MemLp χ ∞ (potentialMeasure d.potential) := hχ.continuous.memLp_of_hasCompactSupport hc
  have hχg : MemLp (fun x => χ x * g x) 2 (potentialMeasure d.potential) := hχtop.mul hg
  have hg2 : Integrable (fun x => χ x ^ 2 * g x ^ 2) (potentialMeasure d.potential) := by
    have hm := hχg.integrable_mul hχg
    apply hm.congr
    exact Eventually.of_forall fun x => by
      change (χ x * g x) * (χ x * g x) = χ x ^ 2 * g x ^ 2
      ring
  have hgb : Integrable (fun x => χ x * g x * sourceVectorCutoffDot χ u x)
      (potentialMeasure d.potential) := hχg.integrable_mul hb
  have hB := integral_source_vector_compact_cutoff_bochner d u Du hu hDu hw hχ hc
  have hl : (∫ x, (χ x * rawWeakSourceVectorAdjoint d.potential u Du x -
        sourceVectorCutoffDot χ u x) ^ 2 ∂potentialMeasure d.potential) =
      (∫ x, χ x ^ 2 * g x ^ 2 ∂potentialMeasure d.potential) -
        2 * (∫ x, χ x * g x * sourceVectorCutoffDot χ u x ∂potentialMeasure d.potential) +
        ∫ x, sourceVectorCutoffDot χ u x ^ 2 ∂potentialMeasure d.potential := by
    calc
      _ = ∫ x, (χ x ^ 2 * g x ^ 2 - 2 * (χ x * g x * sourceVectorCutoffDot χ u x)) +
          sourceVectorCutoffDot χ u x ^ 2 ∂potentialMeasure d.potential := by
        apply integral_congr_ae
        filter_upwards [hadj] with x hx
        rw [hx]
        ring
      _ = _ := by
        have hgb2 : Integrable (fun x => 2 * (χ x * g x * sourceVectorCutoffDot χ u x))
            (potentialMeasure d.potential) := hgb.const_mul 2
        have hsub : Integrable (fun x => χ x ^ 2 * g x ^ 2 -
            2 * (χ x * g x * sourceVectorCutoffDot χ u x)) (potentialMeasure d.potential) := hg2.sub hgb2
        rw [integral_add hsub hb2, integral_sub hg2 hgb2, integral_const_mul]
  have hr : (∫ x, ∑ i : Fin n, ∑ j : Fin n,
        (coordinateHessian d.potential x i j * (χ x * u i x) * (χ x * u j x) +
          sourceVectorCutoffDerivative χ u Du i j x * sourceVectorCutoffDerivative χ u Du j i x)
        ∂potentialMeasure d.potential) =
      (∫ x, χ x ^ 2 * (sourceVectorMass d.potential u x + sourceVectorJacobianEnergy Du x)
        ∂potentialMeasure d.potential) +
        2 * (∫ x, χ x * sourceVectorCutoffCross χ u Du x ∂potentialMeasure d.potential) +
        ∫ x, sourceVectorCutoffDot χ u x ^ 2 ∂potentialMeasure d.potential := by
    calc
      _ = ∫ x, (χ x ^ 2 * (sourceVectorMass d.potential u x + sourceVectorJacobianEnergy Du x) +
          2 * (χ x * sourceVectorCutoffCross χ u Du x)) + sourceVectorCutoffDot χ u x ^ 2
          ∂potentialMeasure d.potential := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          have he := vector_cutoff_bochner_expansion (coordinateHessian d.potential x)
            (fun i j => Du i j x) (fun i => u i x) (fun i => coordinateDerivative χ i x) (χ x)
          simpa only [sourceVectorCutoffDerivative, sourceVectorMass, sourceVectorJacobianEnergy,
            sourceVectorCutoffCross, sourceVectorCutoffDot, mul_assoc] using he
      _ = _ := by
        have hC2 : Integrable (fun x => 2 * (χ x * sourceVectorCutoffCross χ u Du x))
            (potentialMeasure d.potential) := hC.const_mul 2
        have hadd : Integrable (fun x => χ x ^ 2 *
            (sourceVectorMass d.potential u x + sourceVectorJacobianEnergy Du x) +
              2 * (χ x * sourceVectorCutoffCross χ u Du x)) (potentialMeasure d.potential) := hE.add hC2
        rw [integral_add hadd hb2, integral_add hE hC2, integral_const_mul]
  change (∫ x, (χ x * rawWeakSourceVectorAdjoint d.potential u Du x -
    sourceVectorCutoffDot χ u x) ^ 2 ∂potentialMeasure d.potential) = _ at hB
  rw [hl, hr] at hB
  linarith

end KLSConstantImprovement.ActualSourceLocalizedGaffney405
#print axioms KLSConstantImprovement.ActualSourceLocalizedGaffney405.source_vector_mass_integrable
#print axioms KLSConstantImprovement.ActualSourceLocalizedGaffney405.source_vector_cutoff_products_memLp
#print axioms KLSConstantImprovement.ActualSourceLocalizedGaffney405.source_vector_cutoff_energy_integrable
#print axioms KLSConstantImprovement.ActualSourceLocalizedGaffney405.integral_source_vector_localized_gaffney

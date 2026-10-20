import KLSConstantImprovement.ActualSourceCompactConnectionDomains405

/-! The exact compact aggregate connection balance on the actual weak
source. All signed products have already been proved integrable. The
natural mass bound remains an explicit hypothesis. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff NNReal ENNReal
namespace KLSConstantImprovement.ActualSourceCompactConnectionBalance405
open KLS ActualBoundedCanonicalSource ActualBoundedRawMetricDomain
open ActualSourceHessianEvolution405 ActualSourceCurvatureDomains405 ActualSourceConnectionFields405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405 ActualSourceBoundedMassCutoffs405
open ActualSourceBoundedMassConnectionTests405 ActualSourceCompactConnectionDomains405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem integral_actual_compact_connection_balance (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d g) x ≤ C)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i a E, IsCompact E → MemLp (Du i a) 2 (volume.restrict E))
    (hw : ∀ i a, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i a) a)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) :
    (∫ x, χ x ^ 2 * (sourceConnectionTarget d (naturalCanonicalFlux d g) x +
        sourceConnectionGamma d (naturalCanonicalFlux d g) x) ∂potentialMeasure d.potential) =
      (∫ x, χ x ^ 2 * sourceVectorMass d.potential (naturalCanonicalFlux d g) x ∂potentialMeasure d.potential) -
        (∫ x, χ x ^ 2 * sourceConnectionCross d (naturalCanonicalFlux d g) Du x ∂potentialMeasure d.potential) -
        2 * (∫ x, χ x * sourceConnectionBoundary d χ (naturalCanonicalFlux d g) x ∂potentialMeasure d.potential) := by
  let u := naturalCanonicalFlux d g
  let T (i j a : Fin n) (x : Space n) : ℝ :=
    ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
      boundedMassQuadraticDerivative χ u Du i j a x
  let R (i j : Fin n) (x : Space n) : ℝ :=
    (-coordinateHessian d.potential x i j + sourceConnectionCurvature d x i j) *
      boundedMassQuadraticTest χ u i j x
  have ht (i j : Fin n) :=
    actual_boundedMass_compact_quadratic_hessian_evolution d g hC hM Du hu hDu hw hχ hc i j
  have hT (i j a : Fin n) : Integrable (T i j a) (potentialMeasure d.potential) := (ht i j).1 a
  have hR (i j : Fin n) : Integrable (R i j) (potentialMeasure d.potential) := (ht i j).2.1
  obtain ⟨hX, hB, hH, hP, hG⟩ := compact_connection_fields_integrable d g hC hM Du hu hDu hw hχ hc
  change Integrable (fun x => χ x ^ 2 * sourceVectorMass d.potential u x) (potentialMeasure d.potential) at hH
  change Integrable (fun x => χ x ^ 2 * sourceConnectionTarget d u x) (potentialMeasure d.potential) at hP
  change Integrable (fun x => χ x ^ 2 * sourceConnectionGamma d u x) (potentialMeasure d.potential) at hG
  have hLT : (∫ x, ∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, T i j a x
      ∂potentialMeasure d.potential) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∫ x, T i j a x ∂potentialMeasure d.potential := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum Finset.univ (fun a _ => hT i j a)))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => integrable_finsetSum Finset.univ (fun a _ => hT i j a))]
    apply Finset.sum_congr rfl
    intro j _
    exact integral_finsetSum _ (fun a _ => hT i j a)
  have hRT : (∫ x, ∑ i : Fin n, ∑ j : Fin n, R i j x ∂potentialMeasure d.potential) =
      ∑ i : Fin n, ∑ j : Fin n, ∫ x, R i j x ∂potentialMeasure d.potential := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hR i j))]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ (fun j _ => hR i j)
  have hsum : -(∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∫ x, T i j a x ∂potentialMeasure d.potential) =
      ∑ i : Fin n, ∑ j : Fin n, ∫ x, R i j x ∂potentialMeasure d.potential := by
    calc
      _ = ∑ i : Fin n, ∑ j : Fin n, -(∑ a : Fin n, ∫ x, T i j a x ∂potentialMeasure d.potential) := by
        simp only [Finset.sum_neg_distrib]
      _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (ht i j).2.2
  have hTx (x : Space n) : (∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, T i j a x) =
      χ x ^ 2 * sourceConnectionCross d u Du x + 2 * (χ x * sourceConnectionBoundary d χ u x) := by
    simp only [sourceConnectionCross, sourceConnectionBoundary, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro a _
    dsimp only [T, boundedMassQuadraticDerivative, rawCutoffDerivative]
    rw [coordinateDerivative_square hχ]
    ring
  have hRx (x : Space n) : (∑ i : Fin n, ∑ j : Fin n, R i j x) =
      (-χ x ^ 2 * sourceVectorMass d.potential u x + χ x ^ 2 * sourceConnectionTarget d u x) +
        χ x ^ 2 * sourceConnectionGamma d u x := by
    calc
      _ = -χ x ^ 2 * sourceVectorMass d.potential u x +
          χ x ^ 2 * (∑ i : Fin n, ∑ j : Fin n, sourceConnectionCurvature d x i j * u i x * u j x) := by
        simp only [sourceVectorMass, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [R, boundedMassQuadraticTest]
        ring
      _ = _ := by rw [sourceConnectionCurvature_contraction]; ring
  have hLI : (∫ x, ∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, T i j a x ∂potentialMeasure d.potential) =
      (∫ x, χ x ^ 2 * sourceConnectionCross d u Du x ∂potentialMeasure d.potential) +
        2 * (∫ x, χ x * sourceConnectionBoundary d χ u x ∂potentialMeasure d.potential) := by
    calc
      _ = ∫ x, χ x ^ 2 * sourceConnectionCross d u Du x +
          2 * (χ x * sourceConnectionBoundary d χ u x) ∂potentialMeasure d.potential :=
        integral_congr_ae (Eventually.of_forall hTx)
      _ = _ := by rw [integral_add hX (hB.const_mul 2), integral_const_mul]
  have hRI : (∫ x, ∑ i : Fin n, ∑ j : Fin n, R i j x ∂potentialMeasure d.potential) =
      (-(∫ x, χ x ^ 2 * sourceVectorMass d.potential u x ∂potentialMeasure d.potential) +
        (∫ x, χ x ^ 2 * sourceConnectionTarget d u x ∂potentialMeasure d.potential)) +
        ∫ x, χ x ^ 2 * sourceConnectionGamma d u x ∂potentialMeasure d.potential := by
    calc
      _ = ∫ x, (-χ x ^ 2 * sourceVectorMass d.potential u x +
          χ x ^ 2 * sourceConnectionTarget d u x) + χ x ^ 2 * sourceConnectionGamma d u x
          ∂potentialMeasure d.potential := integral_congr_ae (Eventually.of_forall hRx)
      _ = _ := by
        have hneg : Integrable (fun x => -χ x ^ 2 * sourceVectorMass d.potential u x)
            (potentialMeasure d.potential) := by
          apply hH.neg.congr
          exact Eventually.of_forall fun x => by
            change -(χ x ^ 2 * sourceVectorMass d.potential u x) =
              -χ x ^ 2 * sourceVectorMass d.potential u x
            ring
        have hnp : Integrable (fun x => -χ x ^ 2 * sourceVectorMass d.potential u x +
            χ x ^ 2 * sourceConnectionTarget d u x) (potentialMeasure d.potential) := hneg.add hP
        rw [integral_add hnp hG, integral_add hneg hP]
        have hni : (∫ x, -χ x ^ 2 * sourceVectorMass d.potential u x ∂potentialMeasure d.potential) =
            -(∫ x, χ x ^ 2 * sourceVectorMass d.potential u x ∂potentialMeasure d.potential) := by
          simpa only [Pi.neg_apply, neg_mul] using
            integral_neg (fun x => χ x ^ 2 * sourceVectorMass d.potential u x)
        rw [hni]
  have hPG : (∫ x, χ x ^ 2 * (sourceConnectionTarget d u x + sourceConnectionGamma d u x)
      ∂potentialMeasure d.potential) =
      (∫ x, χ x ^ 2 * sourceConnectionTarget d u x ∂potentialMeasure d.potential) +
        ∫ x, χ x ^ 2 * sourceConnectionGamma d u x ∂potentialMeasure d.potential := by
    simp only [mul_add]
    exact integral_add hP hG
  rw [← hLT, ← hRT, hLI, hRI] at hsum
  rw [hPG]
  linarith

end KLSConstantImprovement.ActualSourceCompactConnectionBalance405
#print axioms KLSConstantImprovement.ActualSourceCompactConnectionBalance405.integral_actual_compact_connection_balance

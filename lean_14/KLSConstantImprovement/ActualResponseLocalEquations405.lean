import KLSConstantImprovement.ActualSourceLocalDivergence405
import KLSConstantImprovement.ActualResponseWeakProductTests405
import KLSConstantImprovement.ActualSourceCurvatureDomains405

/-! The local divergence equations in response production are actual
constructed equations, with all coefficient domains discharged from
SourceData. Their products and finite sums contain no supplied PDE. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualResponseLocalEquations405
open KLS ActualBoundedCanonicalSource ActualSourceLocalDivergence405
open ActualResponseWeakProductTests405 ActualQuadraticResponseField405 ActualQuadraticResponseGramLocal405
open ActualSourceQuadraticEta405 ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
open ActualLocalBoundedWeakAlgebra405 ActualSourceHessianEvolution405 ActualSourceCurvatureDomains405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {n : ℕ} {μ : Measure (Space n)}

theorem sourceInverse_entry_local_top (d : SourceData μ) (i j : Fin n)
    (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (fun x => (coordinateHessian d.potential x)⁻¹ i j) ∞ (volume.restrict E) :=
  memLp_inverseHessian_top_on_compact_of_ae_equation d.source_lipschitz d.gradient_lipschitz
    d.target_smooth.continuous (d.hessian_ae.mono fun _ hx => ⟨hx.1, hx.2.1⟩) hE i j

theorem sourceHessianFlux_local_L2 (d : SourceData μ) (i j a : Fin n)
    (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (fun x => ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j)
      2 (volume.restrict E) := by
  have hm : MemLp (fun x => ∑ b : Fin n, (coordinateHessian d.potential x)⁻¹ a b * d.third x i b j)
      2 (volume.restrict E) := memLp_finsetSum Finset.univ fun b _ =>
    (sourceInverse_entry_local_top d a b E hE).mul (d.third_local_L2 i b j E hE)
  simpa only [Matrix.mul_apply, sourceThirdMatrix, Matrix.of_apply] using hm

theorem sourceCurvatureEntry_locallyIntegrable (d : SourceData μ) (i j : Fin n) :
    LocallyIntegrable (fun x => sourceConnectionCurvature d x i j) volume := by
  apply locallyIntegrable_iff.mpr
  intro E hE
  letI : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hE.measure_ne_top
  have hm := KLS.MemLp.restrict_volume_of_potentialMeasure
    (memLp_one_iff_integrable.mpr (actual_connection_curvature_entry_integrable d i j))
    d.source_C1.continuous hE
  exact hm.integrable le_rfl

def sourceHessianEntryEquation (d : SourceData μ) (i j : Fin n) : SourceLocalDivergence d where
  flux := fun a x => ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j
  drift := fun x => coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j
  flux_local := sourceHessianFlux_local_L2 d i j
  drift_local :=
    (locallyIntegrable_of_memLp_two_on_compacts fun E hE =>
      KLS.MemLp.restrict_volume_of_potentialMeasure (d.hessian_entry_memLp i j 2)
        d.source_C1.continuous hE).sub (sourceCurvatureEntry_locallyIntegrable d i j)
  identity := by
    intro ψ hψ hc
    have he := (actual_compact_hessian_evolution d (hψ.of_le (by norm_num)) hc i j).2.2
    have hr : (∫ x, (-coordinateHessian d.potential x i j + sourceConnectionCurvature d x i j) * ψ x
        ∂potentialMeasure d.potential) =
        -(∫ x, (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) * ψ x
          ∂potentialMeasure d.potential) := by
      rw [← integral_neg]
      exact integral_congr_ae (Eventually.of_forall fun x => by ring)
    rw [hr] at he
    exact neg_injective he

def responseRowEquation (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    (i a : Fin n) : SourceLocalDivergence d where
  flux := fun r => quadraticResponseDerivative d hn hμ T i r a
  drift := responseRowDrift d T i a
  flux_local := fun r E hE => (quadratic_response_local_weak_domains d hn hμ T).2.1 i r a E hE
  drift_local := locallyIntegrable_of_memLp_two_on_compacts (responseRowDrift_local_L2 d hn hμ T i a)
  identity := fun _ hψ hc => actual_response_row_drift_compact_test d hn hμ T h12 h23 i a hψ hc

def responseRowTimesEquation (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C)
    (i j : Fin n) : SourceLocalDivergence d :=
  sourceLocalDivergenceSum fun a : Fin n =>
    (responseRowEquation d hn hμ T h12 h23 i a).mulLocal
      (quadraticResponseLocalTest d hn hμ T hC hM j a)

def responseHessianTimesEquation (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C)
    (i j : Fin n) : SourceLocalDivergence d :=
  sourceLocalDivergenceSum fun a : Fin n => sourceLocalDivergenceSum fun b : Fin n =>
    (sourceHessianEntryEquation d a b).mulLocal
      ((quadraticResponseLocalTest d hn hμ T hC hM i a).mul
        (quadraticResponseLocalTest d hn hμ T hC hM j b))

def responseAssembledEquation (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C)
    (i j : Fin n) : SourceLocalDivergence d :=
  sourceLocalDivergenceSum fun k : Fin 3 =>
    ![responseRowTimesEquation d hn hμ T h12 h23 hC hM i j,
      responseRowTimesEquation d hn hμ T h12 h23 hC hM j i,
      responseHessianTimesEquation d hn hμ T hC hM i j] k

end KLSConstantImprovement.ActualResponseLocalEquations405

#print axioms KLSConstantImprovement.ActualResponseLocalEquations405.sourceHessianEntryEquation
#print axioms KLSConstantImprovement.ActualResponseLocalEquations405.responseRowEquation
#print axioms KLSConstantImprovement.ActualResponseLocalEquations405.responseAssembledEquation

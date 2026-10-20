import KLSConstantImprovement.ActualQuadraticResponseRowEquation405
import KLSConstantImprovement.ActualPotentialWeakTests405
import KLSConstantImprovement.ActualQuadraticResponseGramLocal405
import KLSConstantImprovement.ActualLocalCompactWeakTests405
import KLSConstantImprovement.ActualSourceRawHessianEvolution405

/-! Actual response-row and Hessian equations on theta*F and theta*F*F.
All compact weak domains are constructed from the literal F/DF fields.
The natural quadratic mass bound is explicit; no production PDE or
global metric energy of the Gram is assumed. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualResponseWeakProductTests405
open KLS ActualBoundedCanonicalSource ActualSourceNaturalGaffney405 ActualSourceQuadraticEta405
open ActualSourceLocalizedGaffney405 ActualQuadraticResponseField405 ActualTraceResponse405
open ActualQuadraticResponseRowEquation405 ActualQuadraticResponseGramLocal405
open ActualLocalBoundedWeakAlgebra405 ActualLocalCompactWeakTests405 ActualPotentialWeakTests405
open ActualSourceHessianEvolution405 ActualSourceRawHessianEvolution405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {n : ℕ} {μ : Measure (Space n)}

def responseRowDrift (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (i a : Fin n) (x : Space n) : ℝ :=
  actualTraceRawDerivative d T i a x -
    ∑ r : Fin n, coordinateHessian d.potential x r a * quadraticResponseMatrix d T x i r

theorem responseRowDrift_local_L2 (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i a : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (responseRowDrift d T i a) 2 (volume.restrict E) := by
  have hg := KLS.MemLp.restrict_volume_of_potentialMeasure
    (actual_trace_derivative_memLp d T i a) d.source_C1.continuous hE
  exact hg.sub (memLp_finsetSum Finset.univ fun r _ =>
    (KLS.MemLp.restrict_volume_of_potentialMeasure (d.hessian_entry_memLp r a ∞)
      d.source_C1.continuous hE).mul ((quadratic_response_local_weak_domains d hn hμ T).1 i r E hE))

theorem actual_response_row_drift_compact_test (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    (i a : Fin n) {ψ : Space n → ℝ} (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    (∑ r : Fin n, ∫ x, quadraticResponseDerivative d hn hμ T i r a x * coordinateDerivative ψ r x
      ∂potentialMeasure d.potential) =
      ∫ x, responseRowDrift d T i a x * ψ x ∂potentialMeasure d.potential := by
  have he := actual_quadratic_response_differentiated_compact_equation d hn hμ T h12 h23 i a
    (hψ.of_le (by norm_num)) hc
  have hHi (r : Fin n) : LocallyIntegrable (fun x => coordinateHessian d.potential x r a *
      quadraticResponseMatrix d T x i r) volume :=
    locallyIntegrable_of_memLp_two_on_compacts fun E hE =>
      (KLS.MemLp.restrict_volume_of_potentialMeasure (d.hessian_entry_memLp r a ∞)
        d.source_C1.continuous hE).mul ((quadratic_response_local_weak_domains d hn hμ T).1 i r E hE)
  have hHiψ (r : Fin n) : Integrable (fun x => coordinateHessian d.potential x r a *
      quadraticResponseMatrix d T x i r * ψ x) (potentialMeasure d.potential) :=
    integrable_raw_mul_compact_potential d.source_C1.continuous (hHi r) hψ.continuous hc
  have hgψ : Integrable (fun x => actualTraceRawDerivative d T i a x * ψ x)
      (potentialMeasure d.potential) :=
    (actual_trace_derivative_memLp d T i a).integrable_mul
      (memLp_of_continuous_hasCompactSupport d.source_C1.continuous hψ.continuous hc)
  have hsumE : (fun x => (∑ r : Fin n, coordinateHessian d.potential x r a *
      quadraticResponseMatrix d T x i r) * ψ x) =
      fun x => ∑ r : Fin n, coordinateHessian d.potential x r a * quadraticResponseMatrix d T x i r * ψ x := by
    funext x
    rw [Finset.sum_mul]
  have hsumψ : Integrable (fun x => (∑ r : Fin n, coordinateHessian d.potential x r a *
      quadraticResponseMatrix d T x i r) * ψ x) (potentialMeasure d.potential) := by
    rw [hsumE]
    exact integrable_finsetSum Finset.univ fun r _ => hHiψ r
  have hr : (∫ x, responseRowDrift d T i a x * ψ x ∂potentialMeasure d.potential) =
      (∫ x, actualTraceRawDerivative d T i a x * ψ x ∂potentialMeasure d.potential) -
      ∑ r : Fin n, ∫ x, coordinateHessian d.potential x r a * quadraticResponseMatrix d T x i r * ψ x
        ∂potentialMeasure d.potential := by
    calc
      _ = (∫ x, actualTraceRawDerivative d T i a x * ψ x ∂potentialMeasure d.potential) -
          ∫ x, (∑ r : Fin n, coordinateHessian d.potential x r a * quadraticResponseMatrix d T x i r) * ψ x
            ∂potentialMeasure d.potential := by
        rw [← integral_sub hgψ hsumψ]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by dsimp only [responseRowDrift]; ring
      _ = _ := by rw [hsumE, integral_finsetSum Finset.univ (fun r _ => hHiψ r)]
  rw [hr]
  linarith

theorem actual_response_row_compact_rawH1_test (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    (i a : Fin n) {f : Space n → ℝ} {F : Fin n → Space n → ℝ}
    (hf : ∀ E, IsCompact E → MemLp f 2 (volume.restrict E)) (hc : HasCompactSupport f)
    {B : ℝ} (hb : ∀ᵐ x ∂volume, ‖f x‖ ≤ B)
    (hFloc : ∀ r E, IsCompact E → MemLp (F r) 2 (volume.restrict E))
    (hF : ∀ r, HasLocalWeakCoordinateDerivative f (F r) r) :
    (∀ r, Integrable (fun x => quadraticResponseDerivative d hn hμ T i r a x * F r x)
      (potentialMeasure d.potential)) ∧
      Integrable (fun x => responseRowDrift d T i a x * f x) (potentialMeasure d.potential) ∧
      (∑ r : Fin n, ∫ x, quadraticResponseDerivative d hn hμ T i r a x * F r x
        ∂potentialMeasure d.potential) = ∫ x, responseRowDrift d T i a x * f x ∂potentialMeasure d.potential :=
  potential_divergence_bounded_compact_H1_test d
    ((quadratic_response_local_weak_domains d hn hμ T).2.1 i · a)
    (responseRowDrift_local_L2 d hn hμ T i a)
    (fun _ hψ hψc => actual_response_row_drift_compact_test d hn hμ T h12 h23 i a hψ hψc)
    hf hc hb hFloc hF

theorem actual_response_row_times_response_test (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C)
    (i j a b : Fin n) {θ : Space n → ℝ} (hθ : ContDiff ℝ 1 θ) (hc : HasCompactSupport θ) :
    (∑ r : Fin n, ∫ x, quadraticResponseDerivative d hn hμ T i r a x *
      (coordinateDerivative θ r x * quadraticResponseMatrix d T x j b +
        θ x * quadraticResponseDerivative d hn hμ T j b r x) ∂potentialMeasure d.potential) =
      ∫ x, responseRowDrift d T i a x * (θ x * quadraticResponseMatrix d T x j b)
        ∂potentialMeasure d.potential := by
  let f := cutoffLocalRawTest hθ (quadraticResponseLocalTest d hn hμ T hC hM j b)
  have hfc : HasCompactSupport f.value := hc.mul_right
  obtain ⟨B, hB⟩ := compact_localRawTest_bound f hfc
  exact (actual_response_row_compact_rawH1_test d hn hμ T h12 h23 i a
    f.value_local hfc hB f.derivative_local f.weak_derivative).2.2

def responseProductDerivative (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (θ : Space n → ℝ) (i j a b r : Fin n) (x : Space n) : ℝ :=
  coordinateDerivative θ r x * (quadraticResponseMatrix d T x i a * quadraticResponseMatrix d T x j b) +
    θ x * (quadraticResponseDerivative d hn hμ T i a r x * quadraticResponseMatrix d T x j b +
      quadraticResponseMatrix d T x i a * quadraticResponseDerivative d hn hμ T j b r x)

theorem actual_hessian_times_response_product_test (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C)
    (i j a b k l : Fin n) {θ : Space n → ℝ} (hθ : ContDiff ℝ 1 θ) (hc : HasCompactSupport θ) :
    -(∑ r : Fin n, ∫ x, ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x k) r l *
      responseProductDerivative d hn hμ T θ i j a b r x ∂potentialMeasure d.potential) =
      ∫ x, (-coordinateHessian d.potential x k l + sourceConnectionCurvature d x k l) *
        (θ x * (quadraticResponseMatrix d T x i a * quadraticResponseMatrix d T x j b))
          ∂potentialMeasure d.potential := by
  let f := cutoffLocalRawTest hθ ((quadraticResponseLocalTest d hn hμ T hC hM i a).mul
    (quadraticResponseLocalTest d hn hμ T hC hM j b))
  have hfc : HasCompactSupport f.value := hc.mul_right
  obtain ⟨B, hB⟩ := compact_localRawTest_bound f hfc
  exact (actual_compact_raw_hessian_evolution d f.value_local hfc hB
    f.derivative_local f.weak_derivative k l).2.2

end KLSConstantImprovement.ActualResponseWeakProductTests405

#print axioms KLSConstantImprovement.ActualResponseWeakProductTests405.actual_response_row_compact_rawH1_test
#print axioms KLSConstantImprovement.ActualResponseWeakProductTests405.actual_response_row_times_response_test
#print axioms KLSConstantImprovement.ActualResponseWeakProductTests405.actual_hessian_times_response_product_test

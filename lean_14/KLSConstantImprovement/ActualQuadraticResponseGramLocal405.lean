import KLSConstantImprovement.ActualQuadraticResponseGram405
import KLSConstantImprovement.ActualLocalBoundedWeakAlgebra405

/-! Actual local weak derivatives of W_F=F H F^T. Every factor is a
constructed quadratic flux or the actual source Hessian. Mass bounds
remain explicit; no global W form domain or production PDE is assumed. -/
noncomputable section
open Matrix MeasureTheory Filter Set
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualQuadraticResponseGramLocal405
open KLS ActualBoundedCanonicalSource ActualSourceQuadraticEta405 ActualSourceNaturalGaffney405
open ActualSourceLocalizedGaffney405 ActualQuadraticResponseField405 ActualQuadraticResponseGram405
open ActualBoundedRawTestAlgebra405 ActualLocalBoundedWeakAlgebra405
variable {n : ℕ} {μ : Measure (Space n)}
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def quadraticResponseLocalTest (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C)
    (i a : Fin n) : LocalRawTest n where
  value := fun x => quadraticResponseMatrix d T x i a
  derivative := fun b => quadraticResponseDerivative d hn hμ T i a b
  value_local_top := fun E hE => actual_quadratic_response_local_top_of_mass_bound d T hC hM i a hE
  derivative_local := (quadratic_response_local_weak_domains d hn hμ T).2.1 i a
  weak_derivative := (quadratic_response_local_weak_domains d hn hμ T).2.2 i a

def quadraticResponseGramLocalTest (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C)
    (i j : Fin n) : LocalRawTest n :=
  localRawTestSum fun b : Fin n => localRawTestSum fun a : Fin n =>
    ((quadraticResponseLocalTest d hn hμ T hC hM i a).mul
      (LocalRawTest.ofBoundedRawTest (BoundedRawTest.hessian d a b))).mul
        (quadraticResponseLocalTest d hn hμ T hC hM j b)

def quadraticResponseGramRawDerivative (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j r : Fin n) (x : Space n) : ℝ :=
  ∑ b, ∑ a,
    ((quadraticResponseDerivative d hn hμ T i a r x * coordinateHessian d.potential x a b +
      quadraticResponseMatrix d T x i a * d.third x r a b) * quadraticResponseMatrix d T x j b +
      (quadraticResponseMatrix d T x i a * coordinateHessian d.potential x a b) *
        quadraticResponseDerivative d hn hμ T j b r x)

theorem quadraticResponseGramLocalTest_value (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C)
    (i j : Fin n) (x : Space n) :
    (quadraticResponseGramLocalTest d hn hμ T hC hM i j).value x = quadraticResponseGram d T x i j := by
  change (∑ b, ∑ a, (quadraticResponseMatrix d T x i a * coordinateHessian d.potential x a b) *
    quadraticResponseMatrix d T x j b) = _
  simp only [quadraticResponseGram, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]

theorem quadraticResponseGramLocalTest_derivative (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C)
    (i j r : Fin n) (x : Space n) :
    (quadraticResponseGramLocalTest d hn hμ T hC hM i j).derivative r x =
      quadraticResponseGramRawDerivative d hn hμ T i j r x := rfl

theorem actual_quadratic_response_gram_local_weak_domains (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C) :
    (∀ i j E, IsCompact E → MemLp (fun x => quadraticResponseGram d T x i j) 2 (volume.restrict E)) ∧
    (∀ i j r E, IsCompact E → MemLp (quadraticResponseGramRawDerivative d hn hμ T i j r) 2
      (volume.restrict E)) ∧
    (∀ i j r, HasLocalWeakCoordinateDerivative (fun x => quadraticResponseGram d T x i j)
      (quadraticResponseGramRawDerivative d hn hμ T i j r) r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j E hE
    exact (memLp_congr_ae (Eventually.of_forall (quadraticResponseGramLocalTest_value d hn hμ T hC hM i j))).mp
      ((quadraticResponseGramLocalTest d hn hμ T hC hM i j).value_local E hE)
  · intro i j r E hE
    exact (quadraticResponseGramLocalTest d hn hμ T hC hM i j).derivative_local r E hE
  · intro i j r
    exact ((quadraticResponseGramLocalTest d hn hμ T hC hM i j).weak_derivative r).congr_ae
      (Eventually.of_forall (quadraticResponseGramLocalTest_value d hn hμ T hC hM i j))
      (Eventually.of_forall (quadraticResponseGramLocalTest_derivative d hn hμ T hC hM i j r))

end KLSConstantImprovement.ActualQuadraticResponseGramLocal405

#print axioms KLSConstantImprovement.ActualQuadraticResponseGramLocal405.quadraticResponseGramLocalTest_derivative
#print axioms KLSConstantImprovement.ActualQuadraticResponseGramLocal405.actual_quadratic_response_gram_local_weak_domains

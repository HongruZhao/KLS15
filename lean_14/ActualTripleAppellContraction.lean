import TripleTensorKernel
import ActualPairAppellContraction
import ActualFourthCumulantCoordinates
import ActualJointCumulantContraction

/-! Literal identification of every size-three subset contraction with the
unordered-triple fourth-cumulant insertion on the actual previous tensor. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLSBelow25.TripleTensor
open TripleProjection PairTensor
variable {r n : ℕ}

def tripleCoordinateEquiv (e : Triple (r+3)) :
    ((Fin 3→Fin n) × (Fin r→Fin n)) ≃ (Fin (r+3)→Fin n) :=
  (Equiv.sumArrowEquivProdArrow (Fin 3) (Fin r) (Fin n)).symm.trans
    (Equiv.arrowCongr (tripleFrame e) (Equiv.refl (Fin n)))

@[simp] theorem tripleCoordinateEquiv_left (e : Triple (r+3))
    (α : Fin 3→Fin n) (β : Fin r→Fin n) (i : Fin 3) :
    tripleCoordinateEquiv e (α,β) (tripleFrame e (Sum.inl i)) = α i := by
  change Sum.elim α β ((tripleFrame e).symm (tripleFrame e (Sum.inl i)))=α i
  rw [Equiv.symm_apply_apply]
  rfl
@[simp] theorem tripleCoordinateEquiv_right (e : Triple (r+3))
    (α : Fin 3→Fin n) (β : Fin r→Fin n) (i : Fin r) :
    tripleCoordinateEquiv e (α,β) (tripleFrame e (Sum.inr i)) = β i := by
  change Sum.elim α β ((tripleFrame e).symm (tripleFrame e (Sum.inr i)))=β i
  rw [Equiv.symm_apply_apply]
  rfl

theorem tripleFrame_eq_finSum (e : Triple (r+3)) :
    tripleFrame e = finSumEquivOfFinset e.property (KLSBelow25.TripleTensor.complement_card e) := by
  ext i
  rcases i with i|i <;> rfl

end KLSBelow25.TripleTensor
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext
open KLSBelow25.PairTensor KLSBelow25.TripleTensor KLSBelow25.TripleProjection
variable {n r a b d : ℕ}
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem actualSubsetAppellContraction_triple_kernel {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n→ℝ} (hf : MemLp f 2 μ)
    (e : Triple (r+3)) (γ : Fin (r+3)→Fin n) :
    actualSubsetAppellContraction μ f (r+3) e.val γ =
      KLSBelow25.TripleTensor.kernel (actualFourthCumulantArray μ) (actualAppellCoefficient μ f (r+1)) e γ := by
  let : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨⟨α,β⟩,rfl⟩ := (tripleCoordinateEquiv (n:=n) e).surjective γ
  have hh := actualSubsetAppellContraction_reindex_typed hμ.logConcave hf e.val
    e.property (KLSBelow25.TripleTensor.complement_card e) α β
  rw [←tripleFrame_eq_finSum e] at hh
  change actualSubsetAppellContraction μ f (r+3) e.val (tripleCoordinateEquiv e (α,β)) = _ at hh
  rw [hh]
  unfold actualCanonicalAppellContraction KLSBelow25.TripleTensor.kernel KLSBelow25.TripleTensor.kernelInFrame
  simp only [tripleCoordinateEquiv_left,tripleCoordinateEquiv_right]
  apply Finset.sum_congr rfl
  intro m _
  rw [actual_cumulant_four_snoc_coordinate hμ]

theorem actual_triple_kernel_square_eq_canonical {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (e : Triple (r+3)) :
    square (KLSBelow25.TripleTensor.kernel (actualFourthCumulantArray μ)
      (actualAppellCoefficient μ f (r+1)) e) =
        actualCanonicalContractionSquare μ f 3 r := by
  let : IsProbabilityMeasure μ := hμ.isProb
  change (∑ γ, (KLSBelow25.TripleTensor.kernel (actualFourthCumulantArray μ)
    (actualAppellCoefficient μ f (r+1)) e γ)^2) = _
  simp_rw [←actualSubsetAppellContraction_triple_kernel hμ hf e]
  have hh := actualSubsetAppellContraction_square_eq_canonical hμ.logConcave hf e.val
  simpa only [e.property,KLSBelow25.TripleTensor.complement_card e] using hh

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualSubsetAppellContraction_triple_kernel
#print axioms KLS.DeterministicBridgeIntegration.actual_triple_kernel_square_eq_canonical

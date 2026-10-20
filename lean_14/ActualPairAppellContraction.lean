import ActualPairTensorCreationRecurrence
import ActualProperCubicCreation

/-! Literal identification of every size-two subset contraction with the
unordered-pair cubic insertion kernel on the actual previous Appell tensor. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLSBelow25.PairTensor
open PairProjection
variable {r n : ℕ}

def pairCoordinateEquiv (e : Pair (r+2)) :
    ((Fin 2→Fin n) × (Fin r→Fin n)) ≃ (Fin (r+2)→Fin n) :=
  (Equiv.sumArrowEquivProdArrow (Fin 2) (Fin r) (Fin n)).symm.trans
    (Equiv.arrowCongr (pairFrame e) (Equiv.refl (Fin n)))

@[simp] theorem pairCoordinateEquiv_left (e : Pair (r+2))
    (α : Fin 2→Fin n) (β : Fin r→Fin n) (i : Fin 2) :
    pairCoordinateEquiv e (α,β) (pairFrame e (Sum.inl i)) = α i := by
  change Sum.elim α β ((pairFrame e).symm (pairFrame e (Sum.inl i)))=α i
  rw [Equiv.symm_apply_apply]
  rfl
@[simp] theorem pairCoordinateEquiv_right (e : Pair (r+2))
    (α : Fin 2→Fin n) (β : Fin r→Fin n) (i : Fin r) :
    pairCoordinateEquiv e (α,β) (pairFrame e (Sum.inr i)) = β i := by
  change Sum.elim α β ((pairFrame e).symm (pairFrame e (Sum.inr i)))=β i
  rw [Equiv.symm_apply_apply]
  rfl

theorem pairFrame_eq_finSum (e : Pair (r+2)) :
    pairFrame e = finSumEquivOfFinset e.property (complement_card e) := by
  ext i
  rcases i with i|i <;> rfl

end KLSBelow25.PairTensor
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext
open KLSBelow25.PairTensor KLSBelow25.PairProjection
variable {n r a b d : ℕ}
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem actualSubsetAppellContraction_reindex_typed
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    {f : Space n→ℝ} (hf : MemLp f 2 μ) (S : Finset (Fin d))
    (ha : S.card=a) (hb : Sᶜ.card=b) (α : Fin a→Fin n) (β : Fin b→Fin n) :
    actualSubsetAppellContraction μ f d S
      (((Equiv.sumArrowEquivProdArrow (Fin a) (Fin b) (Fin n)).symm.trans
        (Equiv.arrowCongr (finSumEquivOfFinset ha hb) (Equiv.refl (Fin n)))) (α,β)) =
      actualCanonicalAppellContraction μ f a b α β := by
  subst a
  subst b
  exact actualSubsetAppellContraction_reindex hLC hf S α β

theorem actual_cumulant_three_snoc_coordinate {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (α : Fin 2→Fin n) (m : Fin n) :
    cumulantTensor μ 3
      (Fin.snoc (fun j => EuclideanSpace.single (α j) 1) (EuclideanSpace.single m 1)) =
        actualThirdCubicArray μ (α 0) (α 1) m := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hk := actualAppellCoefficient_inner_eq_cumulant hμ.logConcave
    (EuclideanSpace.single m 1) 2 α
  simp only [EuclideanSpace.basisFun_apply] at hk
  rw [←hk,actualAppellCoefficient_two_eq_quadraticCovariance hμ
    (hμ.isotropic.memLp_inner _)]
  change ProbabilityTheory.covariance (fun x => inner ℝ x (EuclideanSpace.single m 1))
    (fun x => x (α 0)*x (α 1)) μ =
      thirdCumulantMatrix μ (MomentMap.coordinateVector (α 0)) (α 1) m
  rw [ProbabilityTheory.covariance_eq_sub (hμ.isotropic.memLp_inner _)
    (hμ.quadraticVarianceEight_unconditional.memLp_coordinate_mul (α 0) (α 1)),
    hμ.isotropic.integral_inner,zero_mul,sub_zero,thirdCumulantMatrix_coordinate_eq_cubic]
  apply integral_congr_ae
  exact .of_forall fun x => by simp [EuclideanSpace.inner_single_right]; ring

theorem actualSubsetAppellContraction_pair_kernel {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n→ℝ} (hf : MemLp f 2 μ)
    (e : Pair (r+2)) (γ : Fin (r+2)→Fin n) :
    actualSubsetAppellContraction μ f (r+2) e.val γ =
      kernel (actualThirdCubicArray μ) (actualAppellCoefficient μ f (r+1)) e γ := by
  let : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨⟨α,β⟩,rfl⟩ := (pairCoordinateEquiv (n:=n) e).surjective γ
  have hh := actualSubsetAppellContraction_reindex_typed hμ.logConcave hf e.val
    e.property (complement_card e) α β
  rw [←pairFrame_eq_finSum e] at hh
  change actualSubsetAppellContraction μ f (r+2) e.val (pairCoordinateEquiv e (α,β)) = _ at hh
  rw [hh]
  unfold actualCanonicalAppellContraction kernel kernelInFrame
  simp only [pairCoordinateEquiv_left,pairCoordinateEquiv_right]
  apply Finset.sum_congr rfl
  intro m _
  rw [actual_cumulant_three_snoc_coordinate hμ]

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualSubsetAppellContraction_pair_kernel

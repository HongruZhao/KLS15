import TripleTensorGramBounds
import TripleTensorAnnihilation
import TripleTensorDisjointAlgebra
import ActualTripleTensorDiagonal
import ActualTripleOverlapOneRepresentative

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace KLSBelow25.TripleTensor
open PairTensor TripleProjection
variable {r : ℕ} {ι : Type*} [Fintype ι]
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem kernel_disjoint_pairing_eq_exchange (κ : ι→ι→ι→ι→ℝ)
    (hκ : ∀ m,Symmetric (fun a : Fin 3→ι => κ (a 0) (a 1) (a 2) m))
    (H : Tensor (ι:=ι) (r+4)) (hH : Symmetric H) :
    pairing (kernel κ H (prefixTriple (r+3))) (kernel κ H (disjointTriple r)) =
      exchange (annihilation κ H) := by
  have he : kernel κ H (disjointTriple r)=
      fun a=>kernel κ H (prefixTriple (r+3)) (a∘swapTriples r) := by
    funext a
    exact (kernel_comp κ hκ H hH (swapTriples r) (prefixTriple (r+3)) a).symm
  rw [he,kernel_prefix_eq_cons κ hκ H hH]
  change pairing (kernelInFrame κ H (consFrame (r+3)))
    (fun a=>kernelInFrame κ H (consFrame (r+3)) (a∘disjointSwap r)) = _
  exact coordinate_disjoint_trace κ H hH

end KLSBelow25.TripleTensor
namespace KLS.DeterministicBridgeIntegration
open KLS KLSBelow25.PairTensor KLSBelow25.TripleTensor KLSBelow25.TripleProjection
variable {n r : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem actual_triple_gram_diagonal_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (H : Tensor (ι:=Fin n) (r+1)) :
    gramValue (actualFourthCumulantArray μ) H 3≤864*square H := by
  exact gramValue_le_of_pairing_le _ H 3 (mul_nonneg (by norm_num) (square_nonneg H))
    (actual_triple_kernel_cross_le hμ H)

theorem actual_triple_gram_two_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (H : Tensor (ι:=Fin n) (r+1)) :
    gramValue (actualFourthCumulantArray μ) H 2≤864*square H := by
  exact gramValue_le_of_pairing_le _ H 2 (mul_nonneg (by norm_num) (square_nonneg H))
    (actual_triple_kernel_cross_le hμ H)

theorem actual_triple_gram_one_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (H : Tensor (ι:=Fin n) (r+3)) (hH : Symmetric H) :
    gramValue (actualFourthCumulantArray μ) H 1≤36*square H := by
  rw [gramValue_eq _ (actualFourthCumulant_first_three_symmetric hμ) H hH
    (prefixTriple (r+2)) (overlapOneTriple r) 1 overlapOne_intersection_card]
  exact actual_triple_overlap_one_representative_le hμ H hH

theorem actual_triple_gram_zero_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (H : Tensor (ι:=Fin n) (r+4)) (hH : Symmetric H)
    (B : ℝ) (hB : 0≤B)
    (hC : ∀ T : Tensor (ι:=Fin n) (r+2),Symmetric T →
      square (creation (actualFourthCumulantArray μ) T)≤B*square T) :
    gramValue (actualFourthCumulantArray μ) H 0≤
      (B/(Nat.choose (r+4) 3 : ℝ)^2)*square H := by
  rw [gramValue_eq _ (actualFourthCumulant_first_three_symmetric hμ) H hH
    (prefixTriple (r+3)) (disjointTriple r) 0 KLSBelow25.TripleTensor.disjoint_intersection_card,
    kernel_disjoint_pairing_eq_exchange _ (actualFourthCumulant_first_three_symmetric hμ) H hH]
  exact annihilation_exchange_le _ H hH B hB hC

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actual_triple_gram_one_le
#print axioms KLS.DeterministicBridgeIntegration.actual_triple_gram_zero_le

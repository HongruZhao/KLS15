import ActualTripleTensorExactCreation
import TripleProjectionAffineCreationBound

/-! Affine creation estimate retaining the actual one-to-three diagonal
square. This is the quantity available for exact selected-row cancellation. -/
noncomputable section
open MeasureTheory
namespace KLS.DeterministicBridgeIntegration
open KLS KLSBelow25.PairTensor KLSBelow25.TripleTensor KLSBelow25.TripleProjection
open KLSBelow25.TripleCreation
variable {n r : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem actual_triple_gram_zero_le_exact {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (H : Tensor (ι:=Fin n) (r+1)) (hH : Symmetric H) :
    gramValue (actualFourthCumulantArray μ) H 0≤
      (exactCap (r+1)/(Nat.choose (r+1) 3 : ℝ)^2)*square H := by
  by_cases hr : r<3
  · rw [gramValue_zero_of_lt_six _ H (by omega)]
    exact mul_nonneg (div_nonneg (exactCap_nonneg _) (sq_nonneg _)) (square_nonneg H)
  · obtain ⟨k,hk⟩ : ∃k,r=k+3 := ⟨r-3,by omega⟩
    subst r
    have hb := actual_triple_gram_zero_le hμ H hH (exactCap (k+4))
      (exactCap_nonneg _) (fun T hT=>actual_triple_creation_square_le_exact hμ (k+1) T hT)
    exact hb

/-- Genuine affine-Q cap for all grades, including the two exceptional
small grades. Q is the literal canonical triple insertion square. -/
theorem actual_triple_creation_square_le_affine {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (r : ℕ) (H : Tensor (ι:=Fin n) (r+1)) (hH : Symmetric H) :
    square (creation (actualFourthCumulantArray μ) H)≤
      affineQ ((r:ℝ)+3)*square (kernel (actualFourthCumulantArray μ) H (prefixTriple r))+
      affineRest (exactCap (r+1)) ((r:ℝ)+3)*square H := by
  have hκ := actualFourthCumulant_first_three_symmetric hμ
  have hG := kernel_gram _ hκ H hH
  have hQ2 := gramValue_two_le_three _ hκ H hH
  have hQ3 := gramValue_three_eq_square _ hκ H hH (prefixTriple r)
  by_cases h0 : r=0
  · subst r
    have hb := sumTriples_sq_le_affine_three _ hG
    rw [triple_sum_toHilbert,toHilbert_norm_sq,hQ3] at hb
    norm_num [affineQ,affineRest,chooseThree,recurrenceMultiplier,exactCap] at hb ⊢
    exact hb
  by_cases h1 : r=1
  · subst r
    have hb := sumTriples_sq_le_affine_four _ hG hQ2
    rw [triple_sum_toHilbert,toHilbert_norm_sq,hQ3] at hb
    norm_num [affineQ,affineRest,chooseThree,recurrenceMultiplier,exactCap] at hb ⊢
    exact hb
  obtain ⟨k,hk⟩ : ∃k,r=k+2 := ⟨r-2,by omega⟩
  subst r
  have hb := sumTriples_sq_le_affine _ hG (by omega : 5≤k+2+3) hQ2
    (actual_triple_gram_one_le hμ H hH) (actual_triple_gram_zero_le_exact hμ H hH)
  rw [triple_sum_toHilbert,toHilbert_norm_sq,hQ3] at hb
  simpa only [Nat.cast_add,Nat.cast_ofNat] using hb

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actual_triple_gram_zero_le_exact
#print axioms KLS.DeterministicBridgeIntegration.actual_triple_creation_square_le_affine

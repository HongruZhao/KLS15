import ActualTripleTensorGramBounds
import TripleProjectionCreationBound
import TripleCreationRecurrenceAlgebra

/-! Genuine all-degree fourth-cumulant triple creation. The one-overlap
channel uses the actual flat-two bound 36; the disjoint channel uses the
previous creation grade through its exact binomial adjoint. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLSBelow25.PairTensor KLSBelow25.TripleTensor KLSBelow25.TripleProjection
variable {n r : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem actual_triple_creation_square_le_five {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (H : Tensor (ι:=Fin n) 3) (hH : Symmetric H) :
    square (creation (actualFourthCumulantArray μ) H)≤
      KLSBelow25.TripleCreation.forcing 864 5*square H := by
  have hG := kernel_gram _ (actualFourthCumulant_first_three_symmetric hμ) H hH
  have hQ0 : gramValue (actualFourthCumulantArray μ) H 0≤
      ((0:ℝ)/(Nat.choose (5-2) 3 : ℝ)^2)*square H := by
    rw [gramValue_zero_of_lt_six _ H (by norm_num)]
    norm_num
  have hb := sumTriples_sq_le_recurrence _ hG (by norm_num : 5≤5)
    (actual_triple_gram_diagonal_le hμ H) (actual_triple_gram_two_le hμ H)
    (actual_triple_gram_one_le hμ H hH) hQ0
  rw [triple_sum_toHilbert,toHilbert_norm_sq] at hb
  norm_num [KLSBelow25.TripleCreation.forcing] at hb ⊢
  exact hb

theorem actual_triple_creation_square_le_recurrence {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (H : Tensor (ι:=Fin n) (r+4)) (hH : Symmetric H)
    (B : ℝ) (hB : 0≤B)
    (hC : ∀ T : Tensor (ι:=Fin n) (r+2),Symmetric T →
      square (creation (actualFourthCumulantArray μ) T)≤B*square T) :
    square (creation (actualFourthCumulantArray μ) H)≤
      (KLSBelow25.TripleCreation.forcing 864 ((r:ℝ)+6)+
        KLSBelow25.TripleCreation.recurrenceMultiplier ((r:ℝ)+6)*B)*square H := by
  have hG := kernel_gram _ (actualFourthCumulant_first_three_symmetric hμ) H hH
  have hb := sumTriples_sq_le_recurrence _ hG (by omega : 5≤r+6)
    (actual_triple_gram_diagonal_le hμ H) (actual_triple_gram_two_le hμ H)
    (actual_triple_gram_one_le hμ H hH) (actual_triple_gram_zero_le hμ H hH B hB hC)
  rw [triple_sum_toHilbert,toHilbert_norm_sq] at hb
  convert hb using 1
  simp only [KLSBelow25.TripleCreation.forcing,
      KLSBelow25.TripleCreation.recurrenceMultiplier,Nat.cast_add,Nat.cast_ofNat,
      show (r:ℝ)+3+3=(r:ℝ)+6 by ring]

/-- Actual ordered Hilbert--Schmidt creation cap at every output grade.
There is no assumed overlap bound, recurrence, or induction endpoint. -/
theorem actual_triple_creation_square_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (r : ℕ) :
    ∀ H : Tensor (ι:=Fin n) (r+1),Symmetric H →
      square (creation (actualFourthCumulantArray μ) H)≤
        KLSBelow25.TripleCreation.closed 864 ((r:ℝ)+3)*square H := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro H hH
    by_cases h0 : r=0
    · subst r
      have hb := creation_square_le_card _ H (actual_triple_kernel_square_le hμ H)
      rw [card_triple] at hb
      norm_num at hb ⊢
      have hc : (864:ℝ)≤KLSBelow25.TripleCreation.closed 864 3 := by
        norm_num [KLSBelow25.TripleCreation.closed,KLSBelow25.TripleCreation.chooseThree]
      exact hb.trans (mul_le_mul_of_nonneg_right hc (square_nonneg H))
    by_cases h1 : r=1
    · subst r
      have hb := creation_square_le_card _ H (actual_triple_kernel_square_le hμ H)
      rw [card_triple] at hb
      norm_num at hb ⊢
      rw [KLSBelow25.TripleCreation.closed_four]
      norm_num
      exact hb
    by_cases h2 : r=2
    · subst r
      have hb := actual_triple_creation_square_le_five hμ H hH
      have hc : KLSBelow25.TripleCreation.forcing 864 5≤
          KLSBelow25.TripleCreation.closed 864 5 := by
        norm_num [KLSBelow25.TripleCreation.forcing,KLSBelow25.TripleCreation.closed,
          KLSBelow25.TripleCreation.chooseThree]
      norm_num only [Nat.cast_ofNat] at *
      simpa using hb.trans (mul_le_mul_of_nonneg_right hc (square_nonneg H))
    obtain ⟨k,hk⟩ : ∃k,r=k+3 := ⟨r-3,by omega⟩
    subst r
    let B := KLSBelow25.TripleCreation.closed 864 ((k:ℝ)+4)
    have hB : 0≤B := KLSBelow25.TripleCreation.closed_nonneg (by norm_num)
      (by have := Nat.cast_nonneg (α:=ℝ) k;linarith)
    have hC : ∀ T : Tensor (ι:=Fin n) (k+2),Symmetric T →
        square (creation (actualFourthCumulantArray μ) T)≤B*square T := by
      intro T hT
      have hh := ih (k+1) (by omega) T hT
      simpa only [B,Nat.cast_add,Nat.cast_one,
        show (k:ℝ)+1+3=(k:ℝ)+4 by ring] using hh
    have hb := actual_triple_creation_square_le_recurrence hμ H hH B hB hC
    have hc := KLSBelow25.TripleCreation.closed_recurrence_ge (L:=864)
      (n:=(k:ℝ)+6) (by norm_num) (by have := Nat.cast_nonneg (α:=ℝ) k;linarith)
    have hc' : KLSBelow25.TripleCreation.forcing 864 ((k:ℝ)+6)+
        KLSBelow25.TripleCreation.recurrenceMultiplier ((k:ℝ)+6)*B≤
        KLSBelow25.TripleCreation.closed 864 ((k:ℝ)+6) := by
      simpa only [B,show (k:ℝ)+6-2=(k:ℝ)+4 by ring] using hc
    convert hb.trans (mul_le_mul_of_nonneg_right hc' (square_nonneg H)) using 1
    simp only [Nat.cast_add,Nat.cast_ofNat,
        show (k:ℝ)+3+3=(k:ℝ)+6 by ring]

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actual_triple_creation_square_le_five
#print axioms KLS.DeterministicBridgeIntegration.actual_triple_creation_square_le_recurrence
#print axioms KLS.DeterministicBridgeIntegration.actual_triple_creation_square_le

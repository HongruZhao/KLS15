import ActualTripleTensorCreationRecurrence
import TripleCreationExactCap

noncomputable section
open MeasureTheory
namespace KLS.DeterministicBridgeIntegration
open KLS KLSBelow25.PairTensor KLSBelow25.TripleTensor KLSBelow25.TripleProjection
open KLSBelow25.TripleCreation
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- Exact finite-grade recursive cap for the genuine triple insertion map. -/
theorem actual_triple_creation_square_le_exact {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (r : ℕ) :
    ∀ H : Tensor (ι:=Fin n) (r+1),Symmetric H →
      square (creation (actualFourthCumulantArray μ) H)≤exactCap (r+3)*square H := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro H hH
    by_cases h0 : r=0
    · subst r
      have hb := creation_square_le_card _ H (actual_triple_kernel_square_le hμ H)
      rw [card_triple] at hb
      norm_num at hb ⊢
      exact hb
    by_cases h1 : r=1
    · subst r
      have hb := creation_square_le_card _ H (actual_triple_kernel_square_le hμ H)
      rw [card_triple] at hb
      norm_num at hb ⊢
      exact hb
    by_cases h2 : r=2
    · subst r
      have hb := actual_triple_creation_square_le_five hμ H hH
      norm_num [exactCap_step 5 (by norm_num),recurrenceMultiplier] at hb ⊢
      exact hb
    obtain ⟨k,hk⟩ : ∃k,r=k+3 := ⟨r-3,by omega⟩
    subst r
    let B := exactCap (k+4)
    have hB : 0≤B := exactCap_nonneg _
    have hC : ∀ T : Tensor (ι:=Fin n) (k+2),Symmetric T →
        square (creation (actualFourthCumulantArray μ) T)≤B*square T := by
      intro T hT
      exact ih (k+1) (by omega) T hT
    have hb := actual_triple_creation_square_le_recurrence hμ H hH B hB hC
    rw [exactCap_step (k+3+3) (by omega)]
    simpa only [B,Nat.cast_add,Nat.cast_ofNat,
      show k+3+3-2=k+4 by omega,show (k:ℝ)+3+3=(k:ℝ)+6 by ring] using hb

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actual_triple_creation_square_le_exact

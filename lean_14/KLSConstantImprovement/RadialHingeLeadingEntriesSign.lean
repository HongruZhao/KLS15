import KLSConstantImprovement.ExponentialPolynomialAlphaRows
import KLSConstantImprovement.RadialHingeEntryRowsSign

/-! Strict positivity of both frozen radial-hinge leading entries for all
alpha,L>=0, from fully instantiated finite certificates. Actual-law block
identification remains separate; no universal curvature theorem is claimed. -/
noncomputable section
namespace KLSConstantImprovement.RadialHingeLeadingEntriesSign
open RadialHingePolynomialData RadialHingeInitialJetEntries RadialHingeEntryRowsSign
open ExponentialPolynomialAlphaRows ExponentialPolynomialIntegerJets
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem alpha_support :
    E11.all (fun t=>decide (t.1 ≤ 18))=true ∧
      O11.all (fun t=>decide (t.1 ≤ 18))=true := by decide

theorem leading_entries_strictly_positive {α L : ℝ} (hα : 0 ≤ α) (hL : 0 ≤ L) :
    0<evalTerms E11 α L ∧ 0<evalTerms O11 α L := by
  have he:∀ t∈E11, t.1 ≤ 18 := by
    intro t ht
    exact of_decide_eq_true ((List.all_eq_true.mp alpha_support.1) t ht)
  have ho:∀ t∈O11, t.1 ≤ 18 := by
    intro t ht
    exact of_decide_eq_true ((List.all_eq_true.mp alpha_support.2) t ht)
  have hE:=evalTerms_zero_le_of_integer_rows E11 (2:ℚ) E11Rows (by norm_num)
    he E11_rows_exact hα (fun a=>E11_row_nonnegative a L hL)
  have hO:=evalTerms_zero_le_of_integer_rows O11 (6:ℚ) O11Rows (by norm_num)
    ho O11_rows_exact hα (fun a=>O11_row_nonnegative a L hL)
  exact ⟨lt_of_lt_of_le (exponential_boundary_leading_positive L).1 hE,
    lt_of_lt_of_le (exponential_boundary_leading_positive L).2 hO⟩

end KLSConstantImprovement.RadialHingeLeadingEntriesSign
#print axioms KLSConstantImprovement.RadialHingeLeadingEntriesSign.leading_entries_strictly_positive

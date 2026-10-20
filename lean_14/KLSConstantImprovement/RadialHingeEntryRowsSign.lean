import KLSConstantImprovement.ExponentialPolynomialIntegerBudget
import KLSConstantImprovement.ExponentialPolynomialCoefficientExpansion

/-! Concrete all-L sign of the original radial-hinge leading-entry alpha rows.
Every initial jet and derivative100 budget is supplied by checked data.
The actual-law block formula is not supplied by this scalar theorem. -/
noncomputable section
namespace KLSConstantImprovement.RadialHingeEntryRowsSign
open RadialHingeInitialJetEntries RadialHingeDominantEntries
open ExponentialPolynomialIntegerJets ExponentialPolynomialIntegerBudget
open ExponentialPolynomialCoefficientExpansion
set_option maxHeartbeats 2000000

theorem entry_support : ∀ a : Fin 19,
    (E11Rows a).all (fun t=>decide (t.1 ≤ 11 ∧ t.2.1 ≤ 6))=true ∧
      (O11Rows a).all (fun t=>decide (t.1 ≤ 11 ∧ t.2.1 ≤ 6))=true := by decide

theorem E11_row_nonnegative (a : Fin 19) :
    ∀ L, 0 ≤ L → 0 ≤ integerPolynomial (E11Rows a) L := by
  have ho:∀ t∈E11Rows a, t.1 ≤ 11 ∧ t.2.1 ≤ 6 := by
    intro t ht
    exact of_decide_eq_true ((List.all_eq_true.mp (entry_support a).1) t ht)
  rcases E11_dominant_budgets_valid a with ⟨hv,hq,hb⟩
  have hu:∀ t∈E11DerivativeRows a, t.1 ≤ 11 ∧ t.2.1 ≤ 6 := by
    intro t ht
    have h:=of_decide_eq_true ((List.all_eq_true.mp hv) t ht)
    exact ⟨h.1,h.2.1⟩
  apply integerPolynomial_nonnegative_of_certificate _ 100
  · intro n hn
    exact E11_initial_jets_nonnegative a ⟨n,hn⟩
  · intro L hL
    rw [integerPolynomial_derivative_eq_checked _ _
      (fun t ht=>(ho t ht).1) (fun t ht=>(ho t ht).2)
      (fun t ht=>(hu t ht).1) (fun t ht=>(hu t ht).2)
      (by norm_num : 11 ≤ 100) (E11_derivative_coefficients_exact a) L]
    exact (entry_derivative_rows_nonnegative a hL).1

theorem O11_row_nonnegative (a : Fin 19) :
    ∀ L, 0 ≤ L → 0 ≤ integerPolynomial (O11Rows a) L := by
  have ho:∀ t∈O11Rows a, t.1 ≤ 11 ∧ t.2.1 ≤ 6 := by
    intro t ht
    exact of_decide_eq_true ((List.all_eq_true.mp (entry_support a).2) t ht)
  rcases O11_dominant_budgets_valid a with ⟨hv,hq,hb⟩
  have hu:∀ t∈O11DerivativeRows a, t.1 ≤ 11 ∧ t.2.1 ≤ 6 := by
    intro t ht
    have h:=of_decide_eq_true ((List.all_eq_true.mp hv) t ht)
    exact ⟨h.1,h.2.1⟩
  apply integerPolynomial_nonnegative_of_certificate _ 100
  · intro n hn
    exact O11_initial_jets_nonnegative a ⟨n,hn⟩
  · intro L hL
    rw [integerPolynomial_derivative_eq_checked _ _
      (fun t ht=>(ho t ht).1) (fun t ht=>(ho t ht).2)
      (fun t ht=>(hu t ht).1) (fun t ht=>(hu t ht).2)
      (by norm_num : 11 ≤ 100) (O11_derivative_coefficients_exact a) L]
    exact (entry_derivative_rows_nonnegative a hL).2

end KLSConstantImprovement.RadialHingeEntryRowsSign
#print axioms KLSConstantImprovement.RadialHingeEntryRowsSign.E11_row_nonnegative
#print axioms KLSConstantImprovement.RadialHingeEntryRowsSign.O11_row_nonnegative

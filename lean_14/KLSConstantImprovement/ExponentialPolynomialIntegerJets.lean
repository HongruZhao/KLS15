import KLSConstantImprovement.ExponentialPolynomialDerivatives
import KLSConstantImprovement.RadialHingeInitialJetEntries

/-! Analytic initial derivative identification for exact integer monomial rows.
The remaining top derivative sign stays an explicit finite certificate premise.
This is an exponential-polynomial theorem, not a universal law estimate. -/
noncomputable section
open scoped BigOperators ContDiff
namespace KLSConstantImprovement.ExponentialPolynomialIntegerJets
open RadialHingeInitialJetEntries ExponentialPolynomialDerivatives
set_option maxHeartbeats 2000000

def realTerms (ts : List JetTerm) : List Monomial :=
  ts.map fun t=>(t.1,(t.2.1:ℝ),(t.2.2:ℝ))
def integerPolynomial (ts : List JetTerm) : ℝ→ℝ := polynomial (realTerms ts)

theorem integerPolynomial_initial_derivative (ts : List JetTerm) (n : ℕ) :
    iteratedDeriv n (integerPolynomial ts) 0=(initialJet ts n:ℝ) := by
  rw [integerPolynomial,polynomial_iteratedDeriv]
  induction ts with
  | nil => simp [realTerms,initialJet]
  | cons t ts ih =>
    change iteratedDeriv n (monomial (t.1,(t.2.1:ℝ),(t.2.2:ℝ))) 0+
      ((realTerms ts).map fun t=>iteratedDeriv n (monomial t) 0).sum =
        (initialJet (t::ts) n:ℝ)
    rw [monomial_initial_derivative,ih]
    by_cases h:t.1 ≤ n <;>
      simp [initialJet,h,Int.cast_add,Int.cast_mul,Int.cast_pow]

theorem integerPolynomial_initial_nonnegative (ts : List JetTerm) (n : ℕ)
    (h : 0 ≤ initialJet ts n) : 0 ≤ iteratedDeriv n (integerPolynomial ts) 0 := by
  rw [integerPolynomial_initial_derivative]
  exact_mod_cast h

theorem integerPolynomial_nonnegative_of_certificate (ts : List JetTerm) (N : ℕ)
    (hinitial : ∀ n, n<N → 0 ≤ initialJet ts n)
    (htop : ∀ L, 0 ≤ L → 0 ≤ iteratedDeriv N (integerPolynomial ts) L) :
    ∀ L, 0 ≤ L → 0 ≤ integerPolynomial ts L := by
  have h := ExponentialPolynomialSign.derivative_chain_nonnegative N
    (fun n=>iteratedDeriv n (integerPolynomial ts))
    (fun n hn L=>polynomial_derivative_chain (realTerms ts) n L)
    (fun n hn=>integerPolynomial_initial_nonnegative ts n (hinitial n hn)) htop
  simpa only [iteratedDeriv_zero] using h

theorem entry_initial_derivatives_nonnegative (a : Fin 19) (n : Fin 100) :
    0 ≤ iteratedDeriv n (integerPolynomial (E11Rows a)) 0 ∧
      0 ≤ iteratedDeriv n (integerPolynomial (O11Rows a)) 0 :=
  ⟨integerPolynomial_initial_nonnegative _ _ (E11_initial_jets_nonnegative a n),
   integerPolynomial_initial_nonnegative _ _ (O11_initial_jets_nonnegative a n)⟩

end KLSConstantImprovement.ExponentialPolynomialIntegerJets
#print axioms KLSConstantImprovement.ExponentialPolynomialIntegerJets.integerPolynomial_initial_derivative
#print axioms KLSConstantImprovement.ExponentialPolynomialIntegerJets.integerPolynomial_nonnegative_of_certificate
#print axioms KLSConstantImprovement.ExponentialPolynomialIntegerJets.entry_initial_derivatives_nonnegative

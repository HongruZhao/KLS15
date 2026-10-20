import ActualTwoRowsAppellDrift

/-! Exact reindexing of both retained canonical charges. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def actualTwoRowsPairCharge (μ : Measure (Space n)) (f : Space n → ℝ)
    (K : ℝ) (s lambda2 : ℕ → ℝ) (d : ℕ) : ℝ :=
  (lambda2 (d-1)*K/s (d-1))*(coupledAppellQ μ f K 2 (d-1))^2

def actualTwoRowsTripleCharge (μ : Measure (Space n)) (f : Space n → ℝ)
    (K : ℝ) (s lambda3 : ℕ → ℝ) (d : ℕ) : ℝ :=
  if 4 ≤ d then (lambda3 (d-2)*K/s (d-2))*(coupledAppellQ μ f K 3 (d-2))^2 else 0

theorem two_rows_charge_inner_eq {K : ℝ} (s lambda2 lambda3 : ℕ → ℝ)
    (Q : ℕ → ℕ → ℝ) (d : ℕ) (hd : 3 ≤ d) :
    (∑ a ∈ Finset.Icc 2 (d-1),
      (twoRowsLambda lambda2 lambda3 a (d-a+1)*K/s (d-a+1))*(Q a (d-a+1))^2) =
    (lambda2 (d-1)*K/s (d-1))*(Q 2 (d-1))^2 +
    (if 4 ≤ d then (lambda3 (d-2)*K/s (d-2))*(Q 3 (d-2))^2 else 0) := by
  classical
  have hp (a : ℕ) :
      (twoRowsLambda lambda2 lambda3 a (d-a+1)*K/s (d-a+1))*(Q a (d-a+1))^2 =
      (if a=2 then (lambda2 (d-1)*K/s (d-1))*(Q 2 (d-1))^2 else 0) +
      (if a=3 then (lambda3 (d-2)*K/s (d-2))*(Q 3 (d-2))^2 else 0) := by
    by_cases h2 : a=2
    · subst a
      have hs : d-2+1=d-1 := by omega
      simp [twoRowsLambda,hs]
    · by_cases h3 : a=3
      · subst a
        have hs : d-3+1=d-2 := by omega
        simp [twoRowsLambda,hs]
      · simp [twoRowsLambda,h2,h3]
  simp_rw [hp]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_Icc]
  have h2 : 2 ≤ d-1 := by omega
  have h3 : 3 ≤ d-1 ↔ 4 ≤ d := by omega
  simp [h2,h3]

theorem actual_two_rows_budget_charge_sum_eq
    {μ : Measure (Space n)} (f : Space n → ℝ) (K : ℝ)
    (s lambda2 lambda3 : ℕ → ℝ) (N : ℕ) :
    (∑ p ∈ coupledDriftPairs N,
      (twoRowsLambda lambda2 lambda3 p.2 (p.1-p.2+1)*K/s (p.1-p.2+1)) *
        (coupledAppellQ μ f K p.2 (p.1-p.2+1))^2) =
    ∑ d ∈ Finset.Icc 3 N,
      (actualTwoRowsPairCharge μ f K s lambda2 d + actualTwoRowsTripleCharge μ f K s lambda3 d) := by
  rw [coupledDriftPairs,Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro d hd
  exact two_rows_charge_inner_eq s lambda2 lambda3 (coupledAppellQ μ f K) d (Finset.mem_Icc.mp hd).1

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actual_two_rows_budget_charge_sum_eq

import SelectiveBudgetTriangleYoung

/-! Retain any selected canonical second-factor squares in the shared
triangle budget. All coefficients are literal; no upper bound for a
selected square is subtracted. -/
noncomputable section
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def selectedRowsPrefix (s : ℕ → ℝ) (rho lambda : ℕ → ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 2 (d-1),
    s (d-a+1)*(rho d a)^2/(1-lambda a (d-a+1))

theorem coupled_triangle_selected_rows_young (N : ℕ) (P : ℕ → ℝ)
    (Q : ℕ → ℕ → ℝ) (s : ℕ → ℝ) (rho lambda : ℕ → ℕ → ℝ) {C K : ℝ}
    (hK : 0 ≤ K) (hs : ∀ b, 2 ≤ b → 0 < s b)
    (hlambda : ∀ a b, 2 ≤ a → 2 ≤ b → lambda a b < 1)
    (hjoint : ∀ b ∈ Finset.Icc 2 N,
      (∑ a ∈ Finset.Icc 2 (N-1), (Q a b)^2) ≤ C*(P b)^2) :
    2*Real.sqrt K*(∑ d ∈ Finset.Icc 3 N, ∑ a ∈ Finset.Icc 2 (d-1),
      rho d a*(P d/(d : ℝ))*Q a (d-a+1)) +
      (∑ p ∈ coupledDriftPairs N,
        (lambda p.2 (p.1-p.2+1)*K/s (p.1-p.2+1))*(Q p.2 (p.1-p.2+1))^2) ≤
      (∑ d ∈ Finset.Icc 3 N, selectedRowsPrefix s rho lambda d*(P d/(d : ℝ))^2) +
      ∑ b ∈ Finset.Icc 2 N, (K*C/s b)*(P b)^2 := by
  classical
  have hp : ∀ p ∈ coupledDriftPairs N, 2 ≤ p.2 ∧ 2 ≤ p.1-p.2+1 := by
    intro p hp
    obtain ⟨hd,ha⟩ := Finset.mem_sigma.mp hp
    simp only [Finset.mem_Icc] at hd ha
    omega
  have hfpos : ∀ p ∈ coupledDriftPairs N, 0 < 1-lambda p.2 (p.1-p.2+1) := by
    intro p hmem
    have hh := hlambda p.2 (p.1-p.2+1) (hp p hmem).1 (hp p hmem).2
    linarith
  have hy := Finset.sum_le_sum (s := coupledDriftPairs N) (fun p hmem =>
    sqrt_weighted_young hK
      (div_pos (hs _ (hp p hmem).2) (hfpos p hmem))
      (rho p.1 p.2*(P p.1/(p.1 : ℝ))) (Q p.2 (p.1-p.2+1)))
  have he : (∑ p ∈ coupledDriftPairs N, 2*Real.sqrt K *
      (rho p.1 p.2*(P p.1/(p.1 : ℝ)))*Q p.2 (p.1-p.2+1)) =
      2*Real.sqrt K*(∑ d ∈ Finset.Icc 3 N, ∑ a ∈ Finset.Icc 2 (d-1),
        rho d a*(P d/(d : ℝ))*Q a (d-a+1)) := by
    rw [coupledDriftPairs,Finset.sum_sigma,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hfirst : (∑ p ∈ coupledDriftPairs N,
      (s (p.1-p.2+1)/(1-lambda p.2 (p.1-p.2+1))) *
        (rho p.1 p.2*(P p.1/(p.1 : ℝ)))^2) =
      ∑ d ∈ Finset.Icc 3 N, selectedRowsPrefix s rho lambda d*(P d/(d : ℝ))^2 := by
    rw [coupledDriftPairs,Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro d hd
    unfold selectedRowsPrefix
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hsecond : (∑ p ∈ coupledDriftPairs N,
      (K/(s (p.1-p.2+1)/(1-lambda p.2 (p.1-p.2+1)))) *
        (Q p.2 (p.1-p.2+1))^2) =
      (∑ p ∈ coupledDriftPairs N, (K/s (p.1-p.2+1)) *
        (Q p.2 (p.1-p.2+1))^2) -
      ∑ p ∈ coupledDriftPairs N,
        (lambda p.2 (p.1-p.2+1)*K/s (p.1-p.2+1))*(Q p.2 (p.1-p.2+1))^2 := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hmem
    field_simp
  rw [he,Finset.sum_add_distrib,hfirst,hsecond] at hy
  have hj := coupled_triangle_second_factor_weighted N P Q (fun b => K/s b)
    (fun b hb => div_nonneg hK (hs b (Finset.mem_Icc.mp hb).1).le) hjoint
  have hj' : (∑ p ∈ coupledDriftPairs N, (K/s (p.1-p.2+1)) *
      (Q p.2 (p.1-p.2+1))^2) ≤ ∑ b ∈ Finset.Icc 2 N, (K*C/s b)*(P b)^2 := by
    convert hj using 1
    apply Finset.sum_congr rfl
    intro b hb
    ring
  linarith

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.coupled_triangle_selected_rows_young

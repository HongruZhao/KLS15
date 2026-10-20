import ActualTwoRowsAppellSplit

/-! Simultaneous literal size-two and size-three drift extraction under
the unchanged previous joint budget. Exact canonical charges are retained
until their genuine creation bounds are supplied. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLSBelow25.PairTensor
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def twoRowsLambda (lambda2 lambda3 : ℕ → ℝ) (a b : ℕ) : ℝ :=
  if a=2 then lambda2 b else if a=3 then lambda3 b else 0

theorem twoRowsProfile_nonneg (theta2 theta3 : ℕ → ℝ)
    (htheta2 : ∀ d, 3 ≤ d → theta2 d ≤ 1)
    (htheta3 : ∀ d, 3 ≤ d → theta3 d ≤ 1) (d a : ℕ) (hd : 3 ≤ d) :
    0 ≤ twoRowsProfile theta2 theta3 d a := by
  unfold twoRowsProfile
  split_ifs
  · linarith [htheta2 d hd]
  · linarith [htheta3 d hd]
  · norm_num

theorem twoRowsLambda_lt_one (lambda2 lambda3 : ℕ → ℝ)
    (hlambda2 : ∀ b, 2 ≤ b → lambda2 b < 1)
    (hlambda3 : ∀ b, 2 ≤ b → lambda3 b < 1)
    (a b : ℕ) (hb : 2 ≤ b) : twoRowsLambda lambda2 lambda3 a b < 1 := by
  unfold twoRowsLambda
  split_ifs
  · exact hlambda2 b hb
  · exact hlambda3 b hb
  · norm_num

theorem actual_weighted_proper_drift_two_rows_retained_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {K C : ℝ}
    (s theta2 theta3 lambda2 lambda3 : ℕ → ℝ)
    (hK : 0 < K) (hs : ∀ b, 2 ≤ b → 0 < s b)
    (htheta2 : ∀ d, 3 ≤ d → theta2 d ≤ 1)
    (htheta3 : ∀ d, 3 ≤ d → theta3 d ≤ 1)
    (hlambda2 : ∀ b, 2 ≤ b → lambda2 b < 1)
    (hlambda3 : ∀ b, 2 ≤ b → lambda3 b < 1) (N : ℕ)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x, (g x)^2 ∂μ)) :
    2*(∑ d ∈ Finset.Icc 3 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d)) +
      (∑ p ∈ coupledDriftPairs N,
        (twoRowsLambda lambda2 lambda3 p.2 (p.1-p.2+1)*K/s (p.1-p.2+1)) *
          (coupledAppellQ μ f K p.2 (p.1-p.2+1))^2) ≤
      (∑ d ∈ Finset.Icc 3 N,
        selectedRowsPrefix s (twoRowsProfile theta2 theta3) (twoRowsLambda lambda2 lambda3) d *
          (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) +
      (∑ b ∈ Finset.Icc 2 N, (K*C/s b)*(b : ℝ)^2 *
        (K^b*(b.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f b) +
      2*(∑ d ∈ Finset.Icc 3 N,
        (theta2 d*(K^d*(d.factorial : ℝ)^2)⁻¹ *
          (actualAppellCoefficient μ f d ⬝ᵥ actualAppellPairContractionSum μ f d) +
        theta3 d*(K^d*(d.factorial : ℝ)^2)⁻¹ *
          (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperTripleContractionSum μ f d))) := by
  have hh := actual_weighted_selected_rows_remainder_le hμ hf s
    (twoRowsProfile theta2 theta3) (twoRowsLambda lambda2 lambda3) hK hs
    (fun d a hd => twoRowsProfile_nonneg theta2 theta3 htheta2 htheta3 d a hd)
    (fun a b _ hb => twoRowsLambda_lt_one lambda2 lambda3 hlambda2 hlambda3 a b hb)
    N hprevious
  have he : (∑ d ∈ Finset.Icc 3 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d)) =
      (∑ d ∈ Finset.Icc 3 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
        (actualAppellCoefficient μ f d ⬝ᵥ
          actualProfileProperRemainder μ f (twoRowsProfile theta2 theta3) d)) +
      (∑ d ∈ Finset.Icc 3 N,
        (theta2 d*(K^d*(d.factorial : ℝ)^2)⁻¹ *
          (actualAppellCoefficient μ f d ⬝ᵥ actualAppellPairContractionSum μ f d) +
        theta3 d*(K^d*(d.factorial : ℝ)^2)⁻¹ *
          (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperTripleContractionSum μ f d))) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [actualAppellProperRemainder_two_rows_split μ f theta2 theta3 d (Finset.mem_Icc.mp hd).1]
    rw [dotProduct_add,dotProduct_add,dotProduct_smul,dotProduct_smul]
    simp only [smul_eq_mul]
    ring
  rw [he]
  linarith

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actual_weighted_proper_drift_two_rows_retained_le

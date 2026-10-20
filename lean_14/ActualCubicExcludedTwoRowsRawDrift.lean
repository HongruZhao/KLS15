import ActualTwoRowsAppellCharges
import ActualCubicExcludedRowsDrift

/-! Cancellation of both literally retained canonical squares against
proved size-two and size-three Young estimates. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem actual_weighted_proper_drift_two_rows_raw_excluding_cubic_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {K C : ℝ}
    (s theta2 theta3 lambda2 lambda3 extra outgoing : ℕ → ℝ)
    (hK : 0 < K) (hs : ∀ b, 2 ≤ b → 0 < s b)
    (htheta2 : ∀ d, 3 ≤ d → theta2 d ≤ 1)
    (htheta3 : ∀ d, 3 ≤ d → theta3 d ≤ 1)
    (hlambda2 : ∀ b, 2 ≤ b → lambda2 b < 1)
    (hlambda3 : ∀ b, 2 ≤ b → lambda3 b < 1) (N : ℕ) (hN : 3 ≤ N)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x, (g x)^2 ∂μ))
    (hyoung : ∀ d ∈ Finset.Icc 4 N,
      2*(theta2 d*(K^d*(d.factorial : ℝ)^2)⁻¹ *
          (actualAppellCoefficient μ f d ⬝ᵥ actualAppellPairContractionSum μ f d) +
        theta3 d*(K^d*(d.factorial : ℝ)^2)⁻¹ *
          (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperTripleContractionSum μ f d)) ≤
      extra d*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d +
        (actualTwoRowsPairCharge μ f K s lambda2 d+actualTwoRowsTripleCharge μ f K s lambda3 d)+outgoing d) :
    2*(∑ d ∈ Finset.Icc 4 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d)) +
      (K/s 2)*(coupledAppellQ μ f K 2 2)^2 ≤
      (∑ d ∈ Finset.Icc 4 N,
        (selectedRowsPrefix s (twoRowsProfile theta2 theta3) (twoRowsLambda lambda2 lambda3) d+extra d)*
          (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) +
      (∑ b ∈ Finset.Icc 2 N, (K*C/s b)*(b : ℝ)^2 *
        (K^b*(b.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f b) +
      ∑ d ∈ Finset.Icc 4 N, outgoing d := by
  have hh := actual_weighted_selected_rows_excluding_cubic_le hμ hf s
    (twoRowsProfile theta2 theta3) (twoRowsLambda lambda2 lambda3) hK hs
    (fun d a hd => twoRowsProfile_nonneg theta2 theta3 htheta2 htheta3 d a hd)
    (fun a b _ hb => twoRowsLambda_lt_one lambda2 lambda3 hlambda2 hlambda3 a b hb)
    N hN hprevious
  have hcharge : (∑ d ∈ Finset.Icc 4 N, ∑ a ∈ Finset.Icc 2 (d-1),
      (twoRowsLambda lambda2 lambda3 a (d-a+1)*K/s (d-a+1))*
        (coupledAppellQ μ f K a (d-a+1))^2) =
      ∑ d ∈ Finset.Icc 4 N,
        (actualTwoRowsPairCharge μ f K s lambda2 d+actualTwoRowsTripleCharge μ f K s lambda3 d) := by
    apply Finset.sum_congr rfl
    intro d hd
    exact two_rows_charge_inner_eq s lambda2 lambda3 (coupledAppellQ μ f K) d
      (by have := (Finset.mem_Icc.mp hd).1; omega)
  rw [hcharge] at hh
  have hdecomp : (∑ d ∈ Finset.Icc 4 N, (K^d*(d.factorial : ℝ)^2)⁻¹*
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d)) =
      (∑ d ∈ Finset.Icc 4 N, (K^d*(d.factorial : ℝ)^2)⁻¹*
        (actualAppellCoefficient μ f d ⬝ᵥ
          actualProfileProperRemainder μ f (twoRowsProfile theta2 theta3) d)) +
      (∑ d ∈ Finset.Icc 4 N,
        (theta2 d*(K^d*(d.factorial : ℝ)^2)⁻¹*
          (actualAppellCoefficient μ f d ⬝ᵥ actualAppellPairContractionSum μ f d)+
        theta3 d*(K^d*(d.factorial : ℝ)^2)⁻¹*
          (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperTripleContractionSum μ f d))) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [actualAppellProperRemainder_two_rows_split μ f theta2 theta3 d
      (by have := (Finset.mem_Icc.mp hd).1; omega)]
    rw [dotProduct_add,dotProduct_add,dotProduct_smul,dotProduct_smul]
    simp only [smul_eq_mul]
    ring
  rw [hdecomp]
  simp only [Finset.sum_add_distrib]
  have hy := Finset.sum_le_sum hyoung
  rw [←Finset.mul_sum] at hy
  simp only [Finset.sum_add_distrib] at hy hh
  have he : (∑ d ∈ Finset.Icc 4 N,
      (selectedRowsPrefix s (twoRowsProfile theta2 theta3) (twoRowsLambda lambda2 lambda3) d+extra d)*
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) =
      (∑ d ∈ Finset.Icc 4 N,
        selectedRowsPrefix s (twoRowsProfile theta2 theta3) (twoRowsLambda lambda2 lambda3) d*
          (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) +
      ∑ d ∈ Finset.Icc 4 N, extra d*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [he]
  linarith

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actual_weighted_proper_drift_two_rows_raw_excluding_cubic_le

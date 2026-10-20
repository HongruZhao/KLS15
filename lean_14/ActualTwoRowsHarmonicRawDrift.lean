import ActualHarmonicTripleAppellDrift
import ActualTwoRowsAppellRawDrift

/-! Simultaneous exact harmonic cancellation of the actual size-two and
size-three insertion rows, retaining the unchanged preceding joint budget.
All creation and canonical-charge bounds are discharged internally. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem actual_weighted_proper_drift_two_rows_harmonic_raw_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {K C : ℝ}
    (s zeta2 zeta3 : ℕ → ℝ) (hK : 0 < K)
    (hs : ∀ b, 2 ≤ b → 0 < s b)
    (hzeta2 : ∀ b, 2 ≤ b → 0 ≤ zeta2 b)
    (hcap2 : ∀ b, 2 ≤ b → 2*zeta2 b < (b : ℝ)*((b : ℝ)+1))
    (hzeta3 : ∀ b, 2 ≤ b → 0 ≤ zeta3 b)
    (hcap3 : ∀ (b : ℕ), 2 ≤ b → tripleHarmonicRatio (b : ℝ)*zeta3 b < 1)
    (N : ℕ)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x, (g x)^2 ∂μ)) :
    2*(∑ d ∈ Finset.Icc 3 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d)) ≤
      (∑ d ∈ Finset.Icc 3 N, twoRowsHarmonicFirstCost s zeta2 zeta3 d *
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)+
      (∑ b ∈ Finset.Icc 2 N, (K*C/s b)*(b : ℝ)^2 *
        (K^b*(b.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f b)+
      ∑ d ∈ Finset.Icc 3 N,
        (harmonicNeighborCharge K s zeta2 (d-1)*
          (K^(d-1)*((d-1).factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f (d-1)+
        if 4 ≤ d then tripleHarmonicNeighborCharge K s zeta3 (d-2)*
          (K^(d-2)*((d-2).factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f (d-2) else 0) := by
  let extra (d : ℕ) := harmonicThetaProfile zeta2 d*harmonicEtaProfile zeta2 d*s (d-1)+
    if 4 ≤ d then tripleHarmonicThetaProfile zeta3 d*tripleHarmonicEtaProfile zeta3 d*s (d-2) else 0
  let outgoing (d : ℕ) := harmonicNeighborCharge K s zeta2 (d-1)*
    (K^(d-1)*((d-1).factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f (d-1)+
    if 4 ≤ d then tripleHarmonicNeighborCharge K s zeta3 (d-2)*
      (K^(d-2)*((d-2).factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f (d-2) else 0
  have ht2 : ∀ d, 3 ≤ d → harmonicThetaProfile zeta2 d ≤ 1 := by
    intro d hd
    have hb : 2 ≤ d-1 := by omega
    exact (harmonicBudgetTheta_lt_one (by exact_mod_cast hb) (hzeta2 _ hb) (hcap2 _ hb)).le
  have ht3 : ∀ d, 3 ≤ d → tripleHarmonicThetaProfile zeta3 d ≤ 1 := by
    intro d _
    exact (tripleHarmonicThetaProfile_lt_one zeta3 hzeta3 hcap3 d).le
  have hl2 : ∀ b, 2 ≤ b → harmonicLambdaProfile zeta2 b < 1 := by
    intro b hb
    exact harmonicBudgetLambda_lt_one (by exact_mod_cast hb) (hcap2 b hb)
  have hl3 : ∀ b, 2 ≤ b → tripleHarmonicLambdaProfile zeta3 b < 1 :=
    tripleHarmonicLambdaProfile_lt_one zeta3 hcap3
  have hyoung (d : ℕ) (hd : d ∈ Finset.Icc 3 N) :
      2*(harmonicThetaProfile zeta2 d*(K^d*(d.factorial : ℝ)^2)⁻¹ *
          (actualAppellCoefficient μ f d ⬝ᵥ actualAppellPairContractionSum μ f d)+
        tripleHarmonicThetaProfile zeta3 d*(K^d*(d.factorial : ℝ)^2)⁻¹ *
          (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperTripleContractionSum μ f d)) ≤
      extra d*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d+
        (actualTwoRowsPairCharge μ f K s (harmonicLambdaProfile zeta2) d+
          actualTwoRowsTripleCharge μ f K s (tripleHarmonicLambdaProfile zeta3) d)+outgoing d := by
    have hd3 := (Finset.mem_Icc.mp hd).1
    have hp := actual_harmonic_pair_young_matching_charge hμ hf hK s zeta2 hs hzeta2 d hd3
    change 2*harmonicThetaProfile zeta2 d*(K^d*(d.factorial : ℝ)^2)⁻¹ *
        (actualAppellCoefficient μ f d ⬝ᵥ actualAppellPairContractionSum μ f d) ≤
      harmonicThetaProfile zeta2 d*harmonicEtaProfile zeta2 d*s (d-1)*
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d+
      actualTwoRowsPairCharge μ f K s (harmonicLambdaProfile zeta2) d+
      harmonicNeighborCharge K s zeta2 (d-1)*
        (K^(d-1)*((d-1).factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f (d-1) at hp
    by_cases hd4 : 4 ≤ d
    · have ht := actual_harmonic_triple_young_matching_charge hμ hf hK s zeta3 hs hzeta3 d hd4
      dsimp only [extra,outgoing]
      simp only [actualAppellProperTripleContractionSum,ite_eq_left hd4]
      nlinarith [hp,ht]
    · dsimp only [extra,outgoing]
      simp only [tripleHarmonicThetaProfile,actualAppellProperTripleContractionSum,
        actualTwoRowsTripleCharge,ite_eq_right hd4]
      nlinarith [hp]
  have h := actual_weighted_proper_drift_two_rows_raw_le hμ hf s
    (harmonicThetaProfile zeta2) (tripleHarmonicThetaProfile zeta3)
    (harmonicLambdaProfile zeta2) (tripleHarmonicLambdaProfile zeta3)
    extra outgoing hK hs ht2 ht3 hl2 hl3 N hprevious hyoung
  have he : (∑ d ∈ Finset.Icc 3 N,
      (selectedRowsPrefix s (twoRowsProfile (harmonicThetaProfile zeta2) (tripleHarmonicThetaProfile zeta3))
        (twoRowsLambda (harmonicLambdaProfile zeta2) (tripleHarmonicLambdaProfile zeta3)) d+extra d)*
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) =
      ∑ d ∈ Finset.Icc 3 N, twoRowsHarmonicFirstCost s zeta2 zeta3 d*
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
    apply Finset.sum_congr rfl
    intro d hd
    have hc := twoRows_harmonic_first_cost_eq s zeta2 zeta3 hzeta2 hcap2 hzeta3 hcap3 d
      (Finset.mem_Icc.mp hd).1
    have hc' : selectedRowsPrefix s
        (twoRowsProfile (harmonicThetaProfile zeta2) (tripleHarmonicThetaProfile zeta3))
        (twoRowsLambda (harmonicLambdaProfile zeta2) (tripleHarmonicLambdaProfile zeta3)) d+extra d =
        twoRowsHarmonicFirstCost s zeta2 zeta3 d := by
      dsimp only [extra]
      linarith [hc]
    rw [hc']
  rw [he] at h
  exact h

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_weighted_proper_drift_two_rows_harmonic_raw_le

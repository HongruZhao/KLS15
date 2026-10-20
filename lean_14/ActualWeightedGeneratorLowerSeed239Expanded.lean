import ActualTwoRowsHarmonicCenteredDrift
import CoupledSeed239ExpandedAlphaRange

/-! Exact parameter matching for the genuine two-row centered generator.
All tensor and drift estimates are actual-law results; this module only
identifies their coefficients with the independently checked rational profile. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
open CoupledEnergy.NumericsSeed239Expanded
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem numericsSeed239Expanded_harmonic_cost_eq (d : ℕ) (hd : 3 ≤ d) :
    twoRowsHarmonicCost K C young zeta2 zeta3 d =
      (K*C/young d)*(d : ℝ)^2+youngPrefix d-pairGain (d-1)-tripleGain (d-2)+
        pairCharge d+tripleCharge d := by
  have hp : properYoungPrefix young d=youngPrefix d :=
    (youngPrefix_eq_sum d (by omega)).symm
  unfold twoRowsHarmonicCost twoRowsHarmonicFirstCost
  rw [hp,ite_eq_left hd]
  change (K*C/young d)*(d : ℝ)^2+
      (youngPrefix d-pairGain (d-1)-
        (if 4 ≤ d then tripleGain (d-2) else 0))+
      pairCharge d+tripleCharge d = _
  by_cases hd4 : 4 ≤ d
  · rw [ite_eq_left hd4]
    ring
  · have hd3 : d=3 := by omega
    subst d
    have he : tripleGain 1=0 := by
      norm_num [tripleGain,zeta3,harmonicRatioDenom,selectedHarmonicDenom]
    rw [ite_eq_right (by omega),he]
    ring

theorem numericsSeed239Expanded_harmonic_head_eq :
    centeredDriftHeadCoefficient alpha (twoRowsHarmonicCost K C young zeta2 zeta3)=head := by
  rw [centeredDriftHeadCoefficient,twoRowsHarmonicCost,twoRowsHarmonicFirstCost_two]
  change 64/(3*(1-alpha 2))-17+
    ((K*C/young 2)*(2:ℝ)^2+0+pairCharge 2+tripleCharge 2)=head
  unfold head
  ring

theorem numericsSeed239Expanded_harmonic_tail_eq (d : ℕ) (hd : 3 ≤ d) :
    centeredDriftTailCoefficient K alpha (twoRowsHarmonicCost K C young zeta2 zeta3) d=coefficient d := by
  have hl : appellGeneralResidualGeneratorLoss alpha d=
      A d*(d : ℝ)^2+(A d-3)*(d : ℝ) := by
    by_cases hdnew : 4 ≤ d ∧ d ≤ 24
    · simp only [appellGeneralResidualGeneratorLoss,
        generalResidualGeneratorLoss,generalResidualA,A,ite_eq_left hdnew]
    · by_cases hd3 : d=3
      · subst d
        norm_num [appellGeneralResidualGeneratorLoss,appellSymmetricCubicGeneratorLoss,A,alpha]
      · have hd2 : d≠2 := by omega
        simp only [appellGeneralResidualGeneratorLoss,
          appellSymmetricCubicGeneratorLoss,appellSymmetricQuadraticGeneratorLoss,
          ite_eq_right hd2,appellGeneratorLoss,A,ite_eq_right hd3,ite_eq_right hdnew]
  unfold centeredDriftTailCoefficient
  rw [hl,numericsSeed239Expanded_harmonic_cost_eq d hd]
  unfold coefficient
  ring

theorem actual_weighted_generator_coefficients_nonpos_seed239_expanded
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) (N : ℕ) (hN : 2 ≤ N)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x,(g x)^2 ∂μ))
    (hstat : ∀ ell : Lp ℝ 2 μ, actualWeightedAppellPairing f ell K N=
      actualWeightedAppellEnergy μ f K N*inner ℝ f ell)
    (hheat : actualWeightedAppellHeatGenerator μ f K N+
      actualWeightedAppellEnergy μ f K N*actualAppellEnergy μ f 1 ≤ 0) :
    (∑ d ∈ Finset.Icc 3 N, coefficient d*
      ((K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d))-
      head*((K^2*(Nat.factorial 2 : ℝ)^2)⁻¹*actualAppellEnergy μ f 2) ≤ 0 := by
  have hh := actual_two_rows_harmonic_generator_coefficients_nonpos hμ f hunit
    young zeta2 zeta3 K_positive young_positive zeta2_nonneg zeta2_cap zeta3_nonneg zeta3_cap
    alpha alpha_nonneg alpha_lt_one alpha_two_ge_third alpha_three_ge_half alpha_le_low_threshold
    N hN hprevious hstat hheat
  have he : (∑ d ∈ Finset.Icc 3 N,
      centeredDriftTailCoefficient K alpha (twoRowsHarmonicCost K C young zeta2 zeta3) d*
        ((K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)) =
      ∑ d ∈ Finset.Icc 3 N, coefficient d*
        ((K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [numericsSeed239Expanded_harmonic_tail_eq d (Finset.mem_Icc.mp hd).1]
  rw [he,numericsSeed239Expanded_harmonic_head_eq] at hh
  exact hh

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.numericsSeed239Expanded_harmonic_cost_eq
#print axioms KLS.DeterministicBridgeNext.actual_weighted_generator_coefficients_nonpos_seed239_expanded

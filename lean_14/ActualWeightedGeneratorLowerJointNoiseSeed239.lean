import ActualCubicJointCoefficients
import CoupledJointNoiseSeed239AlphaRange

/-! Exact parameter matching for the genuine two-row centered generator.
All tensor and drift estimates are actual-law results; this module only
identifies their coefficients with the independently checked rational profile. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
open CoupledEnergy.NumericsJointNoiseSeed239
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem numericsJointNoiseSeed239_harmonic_cost_eq (d : ℕ) (hd : 3 ≤ d) :
    cubicExcludedHarmonicCost K C young zeta2 zeta3 d =
      (K*C/young d)*(d : ℝ)^2+youngPrefix d-pairGain (d-1)-tripleGain (d-2)+
        pairCharge d+tripleCharge d-(if d=3 then young 2-pairGain 2 else 0) := by
  have hp : properYoungPrefix young d=youngPrefix d :=
    (youngPrefix_eq_sum d (by omega)).symm
  by_cases hd3 : d=3
  · subst d
    norm_num [cubicExcludedHarmonicCost,youngPrefix,pairGain,tripleGain,zeta3,
      twoRowsHarmonicFirstCost,properYoungPrefix,young,harmonicBudgetDenom,
      harmonicRatioDenom,selectedHarmonicDenom,pairCharge,tripleCharge,
      harmonicNeighborCharge,tripleHarmonicNeighborCharge]
    ring
  · have hd4 : 4 ≤ d := by omega
    unfold cubicExcludedHarmonicCost twoRowsHarmonicFirstCost
    rw [hp,ite_eq_left hd,ite_eq_left hd4]
    simp only [hd3,ite_false,ite_eq_left hd,ite_eq_left hd4,sub_zero]
    change (K*C/young d)*(d : ℝ)^2+
      (youngPrefix d-pairGain (d-1)-tripleGain (d-2))+pairCharge d+tripleCharge d=_
    ring

theorem numericsJointNoiseSeed239_harmonic_head_eq :
    jointCubicHeadCoefficient K (young 2) alpha (cubicExcludedHarmonicCost K C young zeta2 zeta3)=head := by
  unfold jointCubicHeadCoefficient cubicExcludedHarmonicCost head tripleCharge tripleHarmonicNeighborCharge
  norm_num only [show ¬4 ≤ (2:ℕ) by omega,show ¬3 ≤ (2:ℕ) by omega,ite_false,Nat.cast_ofNat,zero_add,add_zero]
  ring

theorem numericsJointNoiseSeed239_harmonic_tail_eq (d : ℕ) (hd : 3 ≤ d) :
    jointCubicTailCoefficient K alpha (cubicExcludedHarmonicCost K C young zeta2 zeta3) d=coefficient d := by
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
  unfold jointCubicTailCoefficient
  rw [hl,numericsJointNoiseSeed239_harmonic_cost_eq d hd]
  unfold coefficient
  ring

theorem actual_weighted_generator_coefficients_nonpos_joint_noise_seed239
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) (N : ℕ) (hN : 3 ≤ N)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x,(g x)^2 ∂μ))
    (hstat : ∀ ell : Lp ℝ 2 μ, actualWeightedAppellPairing f ell K N=
      actualWeightedAppellEnergy μ f K N*inner ℝ f ell)
    (hheat : actualWeightedAppellHeatGenerator μ f K N+
      actualWeightedAppellEnergy μ f K N*actualAppellEnergy μ f 1 ≤ 0) :
    (∑ d ∈ Finset.Icc 3 N, coefficient d*
      ((K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d))-
      head*((K^2*(Nat.factorial 2 : ℝ)^2)⁻¹*actualAppellEnergy μ f 2) ≤ 0 := by
  have hh := actual_joint_cubic_harmonic_generator_coefficients_nonpos hμ f hunit
    young zeta2 zeta3 K_positive young_positive zeta2_nonneg zeta2_cap zeta3_nonneg zeta3_cap
    alpha alpha_nonneg alpha_lt_one alpha_two_ge_third alpha_three_ge_half alpha_le_low_threshold
    (by norm_num [K,young,alpha]) (by norm_num [K,alpha])
    N hN hprevious hstat hheat
  have he : (∑ d ∈ Finset.Icc 3 N,
      jointCubicTailCoefficient K alpha (cubicExcludedHarmonicCost K C young zeta2 zeta3) d*
        ((K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)) =
      ∑ d ∈ Finset.Icc 3 N, coefficient d*
        ((K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [numericsJointNoiseSeed239_harmonic_tail_eq d (Finset.mem_Icc.mp hd).1]
  rw [he,numericsJointNoiseSeed239_harmonic_head_eq] at hh
  exact hh

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.numericsJointNoiseSeed239_harmonic_cost_eq
#print axioms KLS.DeterministicBridgeNext.actual_weighted_generator_coefficients_nonpos_joint_noise_seed239

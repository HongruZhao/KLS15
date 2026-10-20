import ActualCubicJointCenteredGenerator

/-! Exact coefficient form after the same-test canonical cubic cancellation.
No maximizer or previous-budget premise is concealed in this assembly lemma. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
variable {n : ℕ}
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

 theorem actual_centered_joint_cubic_generator_coefficients_nonpos
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) {K : ℝ} (hK : 0 < K)
    (s : ℝ) (cost beta : ℕ → ℝ)
    (hbeta0 : ∀ d, 2 ≤ d → 0 ≤ beta d)
    (hbeta1 : ∀ d, 2 ≤ d → beta d < 1)
    (hbeta2 : (1 : ℝ)/3 ≤ beta 2) (hbeta3 : (1 : ℝ)/2 ≤ beta 3)
    (hbetalow : ∀ d, 4 ≤ d → d ≤ 24 → beta d ≤ ((d : ℝ)-1)/((d : ℝ)+1))
    (hQcoeff : 2+1/(K*s)-4*(1+1/(6*K))^2/(3*(1-beta 2)) ≤ 0)
    (hRcoeff : 1-8*(1+1/(6*K))^2/(3*(1-beta 2)) ≤ 0)
    (N : ℕ) (hN : 3 ≤ N)
    (hstat : ∀ ell : Lp ℝ 2 μ, actualWeightedAppellPairing f ell K N=
      actualWeightedAppellEnergy μ f K N*inner ℝ f ell)
    (hheat : actualWeightedAppellHeatGenerator μ f K N+
      actualWeightedAppellEnergy μ f K N*actualAppellEnergy μ f 1 ≤ 0)
    (hproper : 2*(∑ d ∈ Finset.Icc 4 N, (K^d*(d.factorial : ℝ)^2)⁻¹*
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d))+
      (K/s)*(coupledAppellQ μ f K 2 2)^2 ≤
      ∑ d ∈ Finset.Icc 2 N, cost d*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) :
    (∑ d ∈ Finset.Icc 3 N, jointCubicTailCoefficient K beta cost d*
      ((K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d))-
      jointCubicHeadCoefficient K s beta cost*
        ((K^2*(Nat.factorial 2 : ℝ)^2)⁻¹*actualAppellEnergy μ f 2) ≤ 0 := by
  classical
  have hlower := actual_centered_joint_cubic_generator_sum_lower hμ f hunit hK s cost N hN beta
    (fun d hd => hbeta0 d (Finset.mem_Icc.mp hd).1)
    (fun d hd => hbeta1 d (Finset.mem_Icc.mp hd).1) hbeta2 hbeta3 hbetalow hQcoeff hRcoeff
    hstat hheat hproper
  have hshift := CoupledEnergy.variable_factorial_weight_energy_shift
    (fun d => actualAppellEnergy μ f d) beta hK hbeta0
    (fun d => actualAppellEnergy_nonneg _ _ _) N (by omega)
  simp only [CoupledEnergy.factorialWeight] at hshift
  have hsum := hshift.trans hlower
  have hset : Finset.Icc 2 N=insert 2 (Finset.Icc 3 N) := by
    ext d
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  have hnot : 2 ∉ Finset.Icc 3 N := by simp
  have he : (∑ d ∈ Finset.Icc 3 N, jointCubicTailCoefficient K beta cost d*
      ((K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d))-
      jointCubicHeadCoefficient K s beta cost*
        ((K^2*(Nat.factorial 2 : ℝ)^2)⁻¹*actualAppellEnergy μ f 2) =
      (∑ d ∈ Finset.Icc 3 N, K*beta (d-1)*(d : ℝ)^2*
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)-
      ∑ d ∈ Finset.Icc 2 N, (jointCubicGeneratorLoss K s beta d+1+cost d)*
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
    rw [hset,Finset.sum_insert hnot]
    have htail : (∑ d ∈ Finset.Icc 3 N, jointCubicTailCoefficient K beta cost d*
        ((K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)) =
        (∑ d ∈ Finset.Icc 3 N, K*beta (d-1)*(d : ℝ)^2*
          (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)-
        ∑ d ∈ Finset.Icc 3 N, (jointCubicGeneratorLoss K s beta d+1+cost d)*
          (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
      rw [←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      have hd2 : d ≠ 2 := by have := (Finset.mem_Icc.mp hd).1; omega
      simp only [jointCubicTailCoefficient,jointCubicGeneratorLoss,hd2,ite_false]
      ring
    rw [htail]
    simp only [jointCubicGeneratorLoss,ite_true,jointCubicHeadCoefficient]
    ring
  rw [he]
  exact sub_nonpos.mpr hsum

 theorem actual_joint_cubic_harmonic_generator_coefficients_nonpos
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) {K C : ℝ}
    (s zeta2 zeta3 : ℕ → ℝ) (hK : 0 < K) (hs : ∀ b, 2 ≤ b → 0 < s b)
    (hzeta2 : ∀ b, 2 ≤ b → 0 ≤ zeta2 b)
    (hcap2 : ∀ b, 2 ≤ b → 2*zeta2 b < (b : ℝ)*((b : ℝ)+1))
    (hzeta3 : ∀ b, 2 ≤ b → 0 ≤ zeta3 b)
    (hcap3 : ∀ (b : ℕ), 2 ≤ b → tripleHarmonicRatio (b : ℝ)*zeta3 b < 1)
    (beta : ℕ → ℝ) (hbeta0 : ∀ d, 2 ≤ d → 0 ≤ beta d)
    (hbeta1 : ∀ d, 2 ≤ d → beta d < 1)
    (hbeta2 : (1 : ℝ)/3 ≤ beta 2) (hbeta3 : (1 : ℝ)/2 ≤ beta 3)
    (hbetalow : ∀ d, 4 ≤ d → d ≤ 24 → beta d ≤ ((d : ℝ)-1)/((d : ℝ)+1))
    (hQcoeff : 2+1/(K*s 2)-4*(1+1/(6*K))^2/(3*(1-beta 2)) ≤ 0)
    (hRcoeff : 1-8*(1+1/(6*K))^2/(3*(1-beta 2)) ≤ 0)
    (N : ℕ) (hN : 3 ≤ N)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x,(g x)^2 ∂μ))
    (hstat : ∀ ell : Lp ℝ 2 μ, actualWeightedAppellPairing f ell K N=
      actualWeightedAppellEnergy μ f K N*inner ℝ f ell)
    (hheat : actualWeightedAppellHeatGenerator μ f K N+
      actualWeightedAppellEnergy μ f K N*actualAppellEnergy μ f 1 ≤ 0) :
    (∑ d ∈ Finset.Icc 3 N, jointCubicTailCoefficient K beta
      (cubicExcludedHarmonicCost K C s zeta2 zeta3) d*
      ((K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d))-
      jointCubicHeadCoefficient K (s 2) beta (cubicExcludedHarmonicCost K C s zeta2 zeta3)*
        ((K^2*(Nat.factorial 2 : ℝ)^2)⁻¹*actualAppellEnergy μ f 2) ≤ 0 :=
  actual_centered_joint_cubic_generator_coefficients_nonpos hμ f hunit hK (s 2)
    (cubicExcludedHarmonicCost K C s zeta2 zeta3) beta hbeta0 hbeta1 hbeta2 hbeta3 hbetalow
    hQcoeff hRcoeff N hN hstat hheat
    (actual_weighted_proper_drift_harmonic_excluding_cubic_le hμ (Lp.memLp f)
      s zeta2 zeta3 hK hs hzeta2 hcap2 hzeta3 hcap3 N hN hprevious)

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_centered_joint_cubic_generator_coefficients_nonpos
#print axioms KLS.DeterministicBridgeNext.actual_joint_cubic_harmonic_generator_coefficients_nonpos

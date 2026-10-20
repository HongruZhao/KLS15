import ActualTwoRowsHarmonicRawDrift
import TwoRowsOutgoingShift
import ActualCenteredGeneratorFromDrift

/-! Both outgoing costs are reindexed into the unchanged energy sum.
The centered generator keeps the full previous joint budget. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def twoRowsHarmonicCost (K C : ℝ) (s zeta2 zeta3 : ℕ → ℝ) (d : ℕ) : ℝ :=
  (K*C/s d)*(d : ℝ)^2+twoRowsHarmonicFirstCost s zeta2 zeta3 d+
    harmonicNeighborCharge K s zeta2 d+tripleHarmonicNeighborCharge K s zeta3 d

theorem twoRowsHarmonicFirstCost_two (s zeta2 zeta3 : ℕ → ℝ) :
    twoRowsHarmonicFirstCost s zeta2 zeta3 2 = 0 := by
  norm_num [twoRowsHarmonicFirstCost,properYoungPrefix]

theorem actual_weighted_proper_drift_two_rows_harmonic_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {K C : ℝ}
    (s zeta2 zeta3 : ℕ → ℝ) (hK : 0 < K) (hs : ∀ b, 2 ≤ b → 0 < s b)
    (hzeta2 : ∀ b, 2 ≤ b → 0 ≤ zeta2 b)
    (hcap2 : ∀ b, 2 ≤ b → 2*zeta2 b < (b : ℝ)*((b : ℝ)+1))
    (hzeta3 : ∀ b, 2 ≤ b → 0 ≤ zeta3 b)
    (hcap3 : ∀ (b : ℕ), 2 ≤ b → tripleHarmonicRatio (b : ℝ)*zeta3 b < 1) (N : ℕ)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x,(g x)^2 ∂μ)) :
    2*(∑ d ∈ Finset.Icc 3 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d)) ≤
      ∑ d ∈ Finset.Icc 2 N, twoRowsHarmonicCost K C s zeta2 zeta3 d*
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
  have hh := actual_weighted_proper_drift_two_rows_harmonic_raw_le hμ hf
    s zeta2 zeta3 hK hs hzeta2 hcap2 hzeta3 hcap3 N hprevious
  have hp := sum_previous_degree_le N (fun b => harmonicNeighborCharge K s zeta2 b*
    (K^b*(b.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f b) (by
      intro b hb
      have hb2 := (Finset.mem_Icc.mp hb).1
      exact mul_nonneg (mul_nonneg (harmonicNeighborCharge_nonneg hK s zeta2 b hb2
        (hs b hb2) (hzeta2 b hb2)) (by positivity)) (actualAppellEnergy_nonneg _ _ _))
  have ht := sum_two_previous_degrees_le N (fun b => tripleHarmonicNeighborCharge K s zeta3 b*
    (K^b*(b.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f b) (by
      intro b hb
      have hb2 := (Finset.mem_Icc.mp hb).1
      exact mul_nonneg (mul_nonneg (tripleHarmonicNeighborCharge_nonneg hK s zeta3 b hb2
        (hs b hb2) (hzeta3 b hb2)) (by positivity)) (actualAppellEnergy_nonneg _ _ _))
  have hfirst : (∑ d ∈ Finset.Icc 3 N, twoRowsHarmonicFirstCost s zeta2 zeta3 d*
      (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) =
      ∑ d ∈ Finset.Icc 2 N, twoRowsHarmonicFirstCost s zeta2 zeta3 d*
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
    apply Finset.sum_subset (by intro d hd; simp only [Finset.mem_Icc] at hd ⊢;omega)
    intro d hd hn
    have hd2 : d=2 := by simp only [Finset.mem_Icc] at hd hn;omega
    subst d
    rw [twoRowsHarmonicFirstCost_two,zero_mul,zero_mul]
  rw [hfirst] at hh
  simp only [Finset.sum_add_distrib] at hh
  have he : (∑ d ∈ Finset.Icc 2 N, twoRowsHarmonicCost K C s zeta2 zeta3 d*
      (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) =
      (∑ d ∈ Finset.Icc 2 N, (K*C/s d)*(d : ℝ)^2*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)+
      (∑ d ∈ Finset.Icc 2 N, twoRowsHarmonicFirstCost s zeta2 zeta3 d*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)+
      (∑ d ∈ Finset.Icc 2 N, harmonicNeighborCharge K s zeta2 d*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d)+
      (∑ d ∈ Finset.Icc 2 N, tripleHarmonicNeighborCharge K s zeta3 d*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) := by
    rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    unfold twoRowsHarmonicCost
    ring
  rw [he]
  linarith

theorem actual_two_rows_harmonic_generator_coefficients_nonpos
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
    (N : ℕ) (hN : 2 ≤ N)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x,(g x)^2 ∂μ))
    (hstat : ∀ ell : Lp ℝ 2 μ, actualWeightedAppellPairing f ell K N=
      actualWeightedAppellEnergy μ f K N*inner ℝ f ell)
    (hheat : actualWeightedAppellHeatGenerator μ f K N+
      actualWeightedAppellEnergy μ f K N*actualAppellEnergy μ f 1 ≤ 0) :
    (∑ d ∈ Finset.Icc 3 N, centeredDriftTailCoefficient K beta (twoRowsHarmonicCost K C s zeta2 zeta3) d*
      ((K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d))-
      centeredDriftHeadCoefficient beta (twoRowsHarmonicCost K C s zeta2 zeta3)*
        ((K^2*(Nat.factorial 2 : ℝ)^2)⁻¹*actualAppellEnergy μ f 2) ≤ 0 :=
  actual_centered_generator_coefficients_nonpos_of_proper_cost hμ f hunit hK
    (twoRowsHarmonicCost K C s zeta2 zeta3) beta hbeta0 hbeta1 hbeta2 hbeta3 hbetalow N hN hstat hheat
    (actual_weighted_proper_drift_two_rows_harmonic_le hμ (Lp.memLp f)
      s zeta2 zeta3 hK hs hzeta2 hcap2 hzeta3 hcap3 N hprevious)

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_two_rows_harmonic_generator_coefficients_nonpos

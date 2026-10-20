import ActualHarmonicSelectiveBudgetDrift

/-! Actual outgoing and centered normalization of the exact harmonic
size-two refinement. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem harmonicFirstCost_two (s zeta : ℕ → ℝ) : harmonicFirstCost s zeta 2 = 0 := by
  norm_num [harmonicFirstCost,properYoungPrefix]

theorem harmonicNeighborCharge_nonneg {K : ℝ} (hK : 0 < K) (s zeta : ℕ → ℝ)
    (b : ℕ) (hb : 2 ≤ b) (hs : 0 < s b) (hz : 0 ≤ zeta b) :
    0 ≤ harmonicNeighborCharge K s zeta b := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hp : 0 ≤ (b : ℝ)^2+5*(b : ℝ)/3-10/3 := by nlinarith
  unfold harmonicNeighborCharge
  exact div_nonneg (mul_nonneg (mul_nonneg hz (by positivity)) hp) (by positivity)

theorem actual_weighted_proper_drift_harmonic_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {K C : ℝ} (s zeta : ℕ → ℝ)
    (hK : 0 < K) (hs : ∀ b, 2 ≤ b → 0 < s b)
    (hzeta : ∀ b, 2 ≤ b → 0 ≤ zeta b)
    (hcap : ∀ b, 2 ≤ b → 2*zeta b < (b : ℝ)*((b : ℝ)+1)) (N : ℕ)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x, (g x)^2 ∂μ)) :
    2*(∑ d ∈ Finset.Icc 3 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d)) ≤
      (∑ d ∈ Finset.Icc 3 N, harmonicFirstCost s zeta d *
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) +
      ∑ b ∈ Finset.Icc 2 N, ((K*C/s b)*(b : ℝ)^2+harmonicNeighborCharge K s zeta b) *
        (K^b*(b.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f b := by
  have h := actual_weighted_proper_drift_harmonic_raw_le hμ hf s zeta hK hs hzeta hcap N hprevious
  have hcharge : (∑ d ∈ Finset.Icc 3 N, harmonicNeighborCharge K s zeta (d-1) *
      (K^(d-1)*((d-1).factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f (d-1)) ≤
      ∑ b ∈ Finset.Icc 2 N, harmonicNeighborCharge K s zeta b *
        (K^b*(b.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f b := by
    apply sum_previous_degree_le N (fun b => harmonicNeighborCharge K s zeta b *
      (K^b*(b.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f b)
    intro b hb
    have hb2 := (Finset.mem_Icc.mp hb).1
    exact mul_nonneg (mul_nonneg (harmonicNeighborCharge_nonneg hK s zeta b hb2
      (hs b hb2) (hzeta b hb2)) (by positivity)) (actualAppellEnergy_nonneg _ _ _)
  have he : (∑ b ∈ Finset.Icc 2 N, ((K*C/s b)*(b : ℝ)^2+harmonicNeighborCharge K s zeta b) *
      (K^b*(b.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f b) =
      (∑ b ∈ Finset.Icc 2 N, (K*C/s b)*(b : ℝ)^2 *
        (K^b*(b.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f b) +
      ∑ b ∈ Finset.Icc 2 N, harmonicNeighborCharge K s zeta b *
        (K^b*(b.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f b := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [he]
  linarith

theorem actual_weighted_centered_full_drift_harmonic_le
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖ = 1) {K C : ℝ} (s zeta : ℕ → ℝ)
    (hK : 0 < K) (hs : ∀ b, 2 ≤ b → 0 < s b)
    (hzeta : ∀ b, 2 ≤ b → 0 ≤ zeta b)
    (hcap : ∀ b, 2 ≤ b → 2*zeta b < (b : ℝ)*((b : ℝ)+1)) (N : ℕ)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x, (g x)^2 ∂μ))
    (hstat : ∀ ell : Lp ℝ 2 μ, actualWeightedAppellPairing f ell K N =
      actualWeightedAppellEnergy μ f K N*inner ℝ f ell) :
    2*(∑ d ∈ Finset.Icc 2 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d)) -
      actualWeightedAppellEnergy μ f K N*actualAppellEnergy μ f 1 ≤
      actualWeightedAppellEnergy μ f K N +
      (∑ d ∈ Finset.Icc 3 N, harmonicFirstCost s zeta d *
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) +
      ∑ b ∈ Finset.Icc 2 N, ((K*C/s b)*(b : ℝ)^2+harmonicNeighborCharge K s zeta b) *
        (K^b*(b.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f b := by
  have ht := actual_weighted_terminal_eq hμ f K N hstat
  have hb : actualAppellEnergy μ f 1 ≤ 1 := by
    rw [actualAppellEnergy_eq_norm_sq]
    simpa only [hunit,one_pow] using fullClassAppellTensor_one_norm_sq_le hμ.logConcave hμ.isotropic f
  have hM := actualWeightedAppellEnergy_nonneg μ f hK N
  have hMb := mul_le_of_le_one_right hM hb
  have hp := actual_weighted_proper_drift_harmonic_le hμ (Lp.memLp f)
    s zeta hK hs hzeta hcap N hprevious
  rw [actual_weighted_proper_drift_sum_eq f K N] at hp
  have he : (∑ d ∈ Finset.Icc 2 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d)) =
      (∑ d ∈ Finset.Icc 2 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
        (actualAppellCoefficient μ f d ⬝ᵥ actualAppellCoefficient μ
          (fun x => inner ℝ x (affineProjectionVector hμ.isotropic f)) d)) +
      ∑ d ∈ Finset.Icc 2 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
        (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [actualAppellLowerDriftTensor_terminal_split hμ.logConcave hμ.isotropic f
      (Finset.mem_Icc.mp hd).1,dotProduct_add]
    ring
  rw [he]
  linarith

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_weighted_proper_drift_harmonic_le
#print axioms KLS.DeterministicBridgeNext.actual_weighted_centered_full_drift_harmonic_le

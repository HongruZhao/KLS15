import ActualSelectiveBudgetAppellDrift
import HarmonicSelectiveBudgetParameters
import ActualPairAppellAffineQ
import ActualThetaCenteredAppellDrift

/-! Actual size-two square cancellation with its optimal harmonic first
cost.  The exact canonical square cancels internally; no reduced joint
budget is assumed. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def harmonicThetaProfile (zeta : ℕ → ℝ) (d : ℕ) : ℝ :=
  harmonicBudgetTheta ((d-1 : ℕ) : ℝ) (zeta (d-1))
def harmonicEtaProfile (zeta : ℕ → ℝ) (d : ℕ) : ℝ :=
  harmonicBudgetEta ((d-1 : ℕ) : ℝ) (zeta (d-1))
def harmonicLambdaProfile (zeta : ℕ → ℝ) (b : ℕ) : ℝ :=
  harmonicBudgetLambda (b : ℝ) (zeta b)
def harmonicFirstCost (s zeta : ℕ → ℝ) (d : ℕ) : ℝ :=
  properYoungPrefix s d - if 3 ≤ d then s (d-1) -
    s (d-1)/harmonicBudgetDenom ((d-1 : ℕ) : ℝ) (zeta (d-1)) else 0
def harmonicNeighborCharge (K : ℝ) (s zeta : ℕ → ℝ) (b : ℕ) : ℝ :=
  zeta b*(b : ℝ)*((b : ℝ)^2+5*(b : ℝ)/3-10/3)/(K*((b : ℝ)+1)*s b)

theorem actual_pair_weighted_young_affineQ_degree
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {K v : ℝ} (hK : 0 < K) (hv : 0 < v)
    (d : ℕ) (hd : 3 ≤ d) :
    2*(K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellPairContractionSum μ f d) ≤
      v*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d +
      (((d : ℝ)-1)/(2*K*(d : ℝ)*v)) *
        (K^(d-1)*((d-1).factorial : ℝ)^2)⁻¹*actualCanonicalContractionSquare μ f 2 (d-2) +
      (((d : ℝ)-1)*(((d : ℝ)-1)^2+5*((d : ℝ)-1)/3-10/3)/(K*(d : ℝ)*v)) *
        (K^(d-1)*((d-1).factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f (d-1) := by
  obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le hd
  have hdr : d = r+3 := by omega
  have hdr1 : d-1 = r+2 := by omega
  have hdr2 : d-2 = r+1 := by omega
  rw [hdr2,hdr1,hdr]
  have h := actualAppellPairContractionSum_weighted_young_affineQ (r := r) hμ hf hK hv
  simp only [CoupledEnergy.factorialWeight] at h
  dsimp only [PairTensor.pairing,dotProduct] at h ⊢
  push_cast
  convert h using 1; ring

theorem actual_harmonic_pair_young_matching_charge
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {K : ℝ} (hK : 0 < K)
    (s zeta : ℕ → ℝ) (hs : ∀ b, 2 ≤ b → 0 < s b)
    (hzeta : ∀ b, 2 ≤ b → 0 ≤ zeta b) (d : ℕ) (hd : 3 ≤ d) :
    2*harmonicThetaProfile zeta d*(K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellPairContractionSum μ f d) ≤
      harmonicThetaProfile zeta d*harmonicEtaProfile zeta d*s (d-1) *
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d +
      actualSelectiveBudgetCharge μ f K s (harmonicLambdaProfile zeta) d +
      harmonicNeighborCharge K s zeta (d-1) *
        (K^(d-1)*((d-1).factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f (d-1) := by
  have hb : 2 ≤ d-1 := by omega
  have hbc : (2 : ℝ) ≤ ((d-1 : ℕ) : ℝ) := by exact_mod_cast hb
  have hz := hzeta (d-1) hb
  have hs' := hs (d-1) hb
  have hη : 0 < harmonicEtaProfile zeta d := harmonicBudgetEta_pos hbc hz
  have hθ : 0 ≤ harmonicThetaProfile zeta d := harmonicBudgetTheta_nonneg hbc hz
  have h := mul_le_mul_of_nonneg_left
    (actual_pair_weighted_young_affineQ_degree hμ hf hK (mul_pos hη hs') d hd) hθ
  have hc : ((d-1 : ℕ) : ℝ) = (d : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num
  have hden := harmonicBudgetDenom_pos hbc hz
  have hcharge : actualSelectiveBudgetCharge μ f K s (harmonicLambdaProfile zeta) d =
      harmonicThetaProfile zeta d * (((d : ℝ)-1)/(2*K*(d : ℝ)*(harmonicEtaProfile zeta d*s (d-1)))) *
        (K^(d-1)*((d-1).factorial : ℝ)^2)⁻¹*actualCanonicalContractionSquare μ f 2 (d-2) := by
    unfold actualSelectiveBudgetCharge
    rw [actual_size_two_budget_charge f hK]
    have he := harmonicBudget_charge_identity hbc hz hK hs'
    have hsub : d-1-1 = d-2 := by omega
    rw [hsub]
    dsimp only [harmonicLambdaProfile]
    rw [he]
    dsimp only [harmonicThetaProfile,harmonicEtaProfile]
    rw [hc]
    ring
  have hrest : harmonicNeighborCharge K s zeta (d-1) =
      harmonicThetaProfile zeta d *
        (((d : ℝ)-1)*(((d : ℝ)-1)^2+5*((d : ℝ)-1)/3-10/3)/
          (K*(d : ℝ)*(harmonicEtaProfile zeta d*s (d-1)))) := by
    unfold harmonicNeighborCharge harmonicThetaProfile harmonicEtaProfile harmonicBudgetTheta harmonicBudgetEta
    have hd0 : (d : ℝ) ≠ 0 := by positivity
    rw [hc] at hden ⊢
    field_simp [ne_of_gt hden,ne_of_gt hK,ne_of_gt hs',hd0]
    ring
  rw [hcharge,hrest]
  nlinarith [h]

theorem actual_weighted_proper_drift_harmonic_raw_le
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
      (∑ b ∈ Finset.Icc 2 N, (K*C/s b)*(b : ℝ)^2 *
        (K^b*(b.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f b) +
      ∑ d ∈ Finset.Icc 3 N, harmonicNeighborCharge K s zeta (d-1) *
        (K^(d-1)*((d-1).factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f (d-1) := by
  have ht : ∀ d, 3 ≤ d → harmonicThetaProfile zeta d ≤ 1 := by
    intro d hd
    have hb : 2 ≤ d-1 := by omega
    exact (harmonicBudgetTheta_lt_one (by exact_mod_cast hb)
      (hzeta _ hb) (hcap _ hb)).le
  have hl : ∀ b, 2 ≤ b → harmonicLambdaProfile zeta b < 1 := by
    intro b hb
    exact harmonicBudgetLambda_lt_one (by exact_mod_cast hb) (hcap b hb)
  have h := actual_weighted_proper_drift_selective_retained_pair_le hμ hf s
    (harmonicThetaProfile zeta) (harmonicLambdaProfile zeta) hK hs ht hl N hprevious
  have hp := Finset.sum_le_sum (s := Finset.Icc 3 N) (fun d hd =>
    actual_harmonic_pair_young_matching_charge hμ hf hK s zeta hs hzeta d (Finset.mem_Icc.mp hd).1)
  have he : (∑ d ∈ Finset.Icc 3 N, 2*harmonicThetaProfile zeta d *
      (K^d*(d.factorial : ℝ)^2)⁻¹ *
        (actualAppellCoefficient μ f d ⬝ᵥ actualAppellPairContractionSum μ f d)) =
      2*(∑ d ∈ Finset.Icc 3 N, harmonicThetaProfile zeta d *
        (K^d*(d.factorial : ℝ)^2)⁻¹ *
          (actualAppellCoefficient μ f d ⬝ᵥ actualAppellPairContractionSum μ f d)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [he,Finset.sum_add_distrib,Finset.sum_add_distrib] at hp
  have hf : (∑ d ∈ Finset.Icc 3 N, harmonicFirstCost s zeta d *
      (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) =
      (∑ d ∈ Finset.Icc 3 N, selectiveDegreePrefix s (harmonicThetaProfile zeta)
        (harmonicLambdaProfile zeta) d*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) +
      ∑ d ∈ Finset.Icc 3 N, harmonicThetaProfile zeta d*harmonicEtaProfile zeta d*s (d-1) *
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    have hd3 := (Finset.mem_Icc.mp hd).1
    have hb : 2 ≤ d-1 := by omega
    have hbc : (2 : ℝ) ≤ ((d-1 : ℕ) : ℝ) := by exact_mod_cast hb
    rw [selectiveDegreePrefix_eq s (harmonicThetaProfile zeta) (harmonicLambdaProfile zeta) hd3]
    have he := harmonicBudget_first_cost hbc (hzeta _ hb) (hcap _ hb)
    dsimp only [harmonicThetaProfile,harmonicEtaProfile,harmonicLambdaProfile]
    unfold harmonicFirstCost
    rw [ite_eq_left hd3]
    have he' : s (d-1)/harmonicBudgetDenom ((d-1 : ℕ) : ℝ) (zeta (d-1)) =
        s (d-1)*((1-harmonicBudgetTheta ((d-1 : ℕ) : ℝ) (zeta (d-1)))^2 /
          (1-harmonicBudgetLambda ((d-1 : ℕ) : ℝ) (zeta (d-1))) +
          harmonicBudgetTheta ((d-1 : ℕ) : ℝ) (zeta (d-1))*
            harmonicBudgetEta ((d-1 : ℕ) : ℝ) (zeta (d-1))) := by
      rw [he]
      ring
    rw [he']
    ring
  rw [hf]
  linarith

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_harmonic_pair_young_matching_charge
#print axioms KLS.DeterministicBridgeNext.actual_weighted_proper_drift_harmonic_raw_le

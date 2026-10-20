import ActualThetaWeightedAppellDrift
import SelectiveBudgetTriangleYoung

/-! The exact selected canonical square in the literal Appell drift.
The preceding joint budget C is unchanged; the selected square is kept
on the left until it is matched to an actual creation estimate. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def actualSelectiveBudgetCharge (μ : Measure (Space n)) (f : Space n → ℝ)
    (K : ℝ) (s lambda : ℕ → ℝ) (d : ℕ) : ℝ :=
  (lambda (d-1)*K/s (d-1))*(coupledAppellQ μ f K 2 (d-1))^2

theorem actual_size_two_budget_charge {μ : Measure (Space n)} (f : Space n → ℝ)
    {K : ℝ} (hK : 0 < K) (s lambda : ℕ → ℝ) (b : ℕ) :
    (lambda b*K/s b)*(coupledAppellQ μ f K 2 b)^2 =
      (lambda b*(b : ℝ)^2/(4*K*s b)) *
        (K^b*(b.factorial : ℝ)^2)⁻¹ * actualCanonicalContractionSquare μ f 2 (b-1) := by
  rw [coupledAppellQ_sq f hK,coupledAppellScale_sq hK]
  norm_num only [Nat.factorial, Nat.cast_ofNat]
  field_simp

theorem actual_weighted_selective_remainder_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {K C : ℝ} (s theta lambda : ℕ → ℝ)
    (hK : 0 < K) (hs : ∀ b, 2 ≤ b → 0 < s b)
    (htheta : ∀ d, 3 ≤ d → theta d ≤ 1)
    (hlambda : ∀ b, 2 ≤ b → lambda b < 1) (N : ℕ)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x, (g x)^2 ∂μ)) :
    2*(∑ d ∈ Finset.Icc 3 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualThetaProperRemainder μ f theta d)) +
      (∑ d ∈ Finset.Icc 3 N, actualSelectiveBudgetCharge μ f K s lambda d) ≤
      (∑ d ∈ Finset.Icc 3 N, selectiveDegreePrefix s theta lambda d *
        (K^d*(d.factorial : ℝ)^2)⁻¹ * actualAppellEnergy μ f d) +
      ∑ b ∈ Finset.Icc 2 N, (K*C/s b)*(b : ℝ)^2 *
        (K^b*(b.factorial : ℝ)^2)⁻¹ * actualAppellEnergy μ f b := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hper (d : ℕ) (hd : d ∈ Finset.Icc 3 N) :
      (K^d*(d.factorial : ℝ)^2)⁻¹ *
        (actualAppellCoefficient μ f d ⬝ᵥ actualThetaProperRemainder μ f theta d) ≤
      Real.sqrt K*(∑ a ∈ Finset.Icc 2 (d-1), thetaTriangleCoefficient theta d a *
        (coupledAppellP μ f K d/(d : ℝ))*coupledAppellQ μ f K a (d-a+1)) := by
    have hh := mul_le_mul_of_nonneg_left
      (actual_theta_pairing_le_canonical_sum hμ.logConcave hf theta d
        (htheta d (Finset.mem_Icc.mp hd).1))
      (show 0 ≤ (K^d*(d.factorial : ℝ)^2)⁻¹ by positivity)
    calc
      _ ≤ _ := hh
      _ = _ := by
        rw [←mul_assoc,Finset.mul_sum,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        have he := coupledAppell_normalized_term (μ := μ) f hK
          (Finset.mem_Icc.mp hd).1 ha
        calc
          _ = thetaTriangleCoefficient theta d a *
              ((K^d*(d.factorial : ℝ)^2)⁻¹ * Real.sqrt (actualAppellEnergy μ f d) *
                ((d.choose a : ℝ)*Real.sqrt (actualCanonicalContractionSquare μ f a (d-a)))) := by ring
          _ = _ := by rw [he]; ring
  have hsum := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper)
    (by norm_num : (0 : ℝ) ≤ 2)
  rw [←Finset.mul_sum] at hsum
  have hy := coupled_triangle_selective_budget_young N (coupledAppellP μ f K)
    (coupledAppellQ μ f K) s theta lambda hK.le hs hlambda
    (fun b hb => coupledAppellQ_joint_square_le hμ f hK N hprevious hb)
  have hfirst : (∑ d ∈ Finset.Icc 3 N, selectiveDegreePrefix s theta lambda d *
      (coupledAppellP μ f K d/(d : ℝ))^2) =
      ∑ d ∈ Finset.Icc 3 N, selectiveDegreePrefix s theta lambda d *
        (K^d*(d.factorial : ℝ)^2)⁻¹ * actualAppellEnergy μ f d := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [coupledAppellP_div_sq f hK (by have := (Finset.mem_Icc.mp hd).1; omega)]
    ring
  rw [hfirst] at hy
  simp_rw [coupledAppellP_sq f hK] at hy
  have hr : (∑ b ∈ Finset.Icc 2 N, (K*C/s b) *
      ((b : ℝ)^2*(K^b*(b.factorial : ℝ)^2)⁻¹ * actualAppellEnergy μ f b)) =
      ∑ b ∈ Finset.Icc 2 N, (K*C/s b)*(b : ℝ)^2 *
        (K^b*(b.factorial : ℝ)^2)⁻¹ * actualAppellEnergy μ f b := by
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [hr] at hy
  change _ + (∑ d ∈ Finset.Icc 3 N, actualSelectiveBudgetCharge μ f K s lambda d) ≤ _ at hy
  have hsum' : 2*(∑ d ∈ Finset.Icc 3 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualThetaProperRemainder μ f theta d)) ≤
      2*Real.sqrt K * (∑ d ∈ Finset.Icc 3 N,
        ∑ a ∈ Finset.Icc 2 (d-1), thetaTriangleCoefficient theta d a *
          (coupledAppellP μ f K d/(d : ℝ))*coupledAppellQ μ f K a (d-a+1)) := by
    convert hsum using 1; ring
  linarith

theorem actual_weighted_proper_drift_selective_retained_pair_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {K C : ℝ} (s theta lambda : ℕ → ℝ)
    (hK : 0 < K) (hs : ∀ b, 2 ≤ b → 0 < s b)
    (htheta : ∀ d, 3 ≤ d → theta d ≤ 1)
    (hlambda : ∀ b, 2 ≤ b → lambda b < 1) (N : ℕ)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x, (g x)^2 ∂μ)) :
    2*(∑ d ∈ Finset.Icc 3 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d)) +
      (∑ d ∈ Finset.Icc 3 N, actualSelectiveBudgetCharge μ f K s lambda d) ≤
      (∑ d ∈ Finset.Icc 3 N, selectiveDegreePrefix s theta lambda d *
        (K^d*(d.factorial : ℝ)^2)⁻¹ * actualAppellEnergy μ f d) +
      (∑ b ∈ Finset.Icc 2 N, (K*C/s b)*(b : ℝ)^2 *
        (K^b*(b.factorial : ℝ)^2)⁻¹ * actualAppellEnergy μ f b) +
      2*(∑ d ∈ Finset.Icc 3 N, theta d * (K^d*(d.factorial : ℝ)^2)⁻¹ *
        (actualAppellCoefficient μ f d ⬝ᵥ actualAppellPairContractionSum μ f d)) := by
  have h := actual_weighted_selective_remainder_le hμ hf s theta lambda hK hs htheta hlambda N hprevious
  have he : (∑ d ∈ Finset.Icc 3 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d)) =
      (∑ d ∈ Finset.Icc 3 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
        (actualAppellCoefficient μ f d ⬝ᵥ actualThetaProperRemainder μ f theta d)) +
      ∑ d ∈ Finset.Icc 3 N, theta d * (K^d*(d.factorial : ℝ)^2)⁻¹ *
        (actualAppellCoefficient μ f d ⬝ᵥ actualAppellPairContractionSum μ f d) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [actualThetaProperRemainder_pairing_split μ f theta d (Finset.mem_Icc.mp hd).1]
    ring
  rw [he]
  linarith

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_size_two_budget_charge
#print axioms KLS.DeterministicBridgeNext.actual_weighted_proper_drift_selective_retained_pair_le

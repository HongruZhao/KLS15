import ActualThetaAppellRemainder
import ActualPairAppellYoung
import ActualDegreeWeightedTriangleAppellDrift

/-! Actual proper drift after extracting a fraction of the size-two
insertion.  The preceding all-test joint budget is unchanged.  Both an
exact retained pair term and its neighboring-energy Young bound are given. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem actual_weighted_theta_remainder_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {K C : ℝ} (s theta : ℕ → ℝ)
    (hK : 0 < K) (hs : ∀ b, 2 ≤ b → 0 < s b)
    (htheta : ∀ d, 3 ≤ d → theta d ≤ 1) (N : ℕ)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x, (g x)^2 ∂μ)) :
    2*(∑ d ∈ Finset.Icc 3 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualThetaProperRemainder μ f theta d)) ≤
      (∑ d ∈ Finset.Icc 3 N, thetaDegreePrefix s theta d *
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
  have hy := coupled_triangle_theta_weighted_young N (coupledAppellP μ f K)
    (coupledAppellQ μ f K) s theta hK.le
    (fun b hb => hs b (Finset.mem_Icc.mp hb).1)
    (fun b hb => coupledAppellQ_joint_square_le hμ f hK N hprevious hb)
  have hfirst : (∑ d ∈ Finset.Icc 3 N, thetaDegreePrefix s theta d *
      (coupledAppellP μ f K d/(d : ℝ))^2) =
      ∑ d ∈ Finset.Icc 3 N, thetaDegreePrefix s theta d *
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
  exact hsum.trans (by convert hy using 1; ring)

theorem actual_weighted_proper_drift_retained_pair_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {K C : ℝ} (s theta : ℕ → ℝ)
    (hK : 0 < K) (hs : ∀ b, 2 ≤ b → 0 < s b)
    (htheta : ∀ d, 3 ≤ d → theta d ≤ 1) (N : ℕ)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x, (g x)^2 ∂μ)) :
    2*(∑ d ∈ Finset.Icc 3 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d)) ≤
      (∑ d ∈ Finset.Icc 3 N, thetaDegreePrefix s theta d *
        (K^d*(d.factorial : ℝ)^2)⁻¹ * actualAppellEnergy μ f d) +
      (∑ b ∈ Finset.Icc 2 N, (K*C/s b)*(b : ℝ)^2 *
        (K^b*(b.factorial : ℝ)^2)⁻¹ * actualAppellEnergy μ f b) +
      2*(∑ d ∈ Finset.Icc 3 N, theta d * (K^d*(d.factorial : ℝ)^2)⁻¹ *
        (actualAppellCoefficient μ f d ⬝ᵥ actualAppellPairContractionSum μ f d)) := by
  have h := actual_weighted_theta_remainder_le hμ hf s theta hK hs htheta N hprevious
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

theorem actual_pair_weighted_young_degree
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {K v : ℝ} (hK : 0 < K) (hv : 0 < v)
    (d : ℕ) (hd : 3 ≤ d) :
    2*(K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellPairContractionSum μ f d) ≤
      v*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d +
      (((d : ℝ)-1)*((d : ℝ)-1/3)/(K*v)) *
        (K^(d-1)*((d-1).factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f (d-1) := by
  obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le hd
  have hdr : d = r+3 := by omega
  have hdr1 : d-1 = r+2 := by omega
  rw [hdr1,hdr]
  have h := actualAppellPairContractionSum_weighted_young (r := r) hμ hf hK hv
  simp only [CoupledEnergy.factorialWeight] at h
  dsimp only [PairTensor.pairing,dotProduct] at h ⊢
  push_cast
  convert h using 1; ring

theorem actual_weighted_proper_drift_theta_young_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {K C : ℝ} (s theta eta : ℕ → ℝ)
    (hK : 0 < K) (hs : ∀ b, 2 ≤ b → 0 < s b)
    (htheta0 : ∀ d, 3 ≤ d → 0 ≤ theta d)
    (htheta1 : ∀ d, 3 ≤ d → theta d ≤ 1)
    (heta : ∀ d, 3 ≤ d → 0 < eta d) (N : ℕ)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x, (g x)^2 ∂μ)) :
    2*(∑ d ∈ Finset.Icc 3 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d)) ≤
      (∑ d ∈ Finset.Icc 3 N,
        (triangleDegreePrefix s d-theta d*(2-theta d-eta d)*s (d-1)) *
          (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) +
      (∑ b ∈ Finset.Icc 2 N, (K*C/s b)*(b : ℝ)^2 *
        (K^b*(b.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f b) +
      ∑ d ∈ Finset.Icc 3 N,
        (theta d*((d : ℝ)-1)*((d : ℝ)-1/3)/(K*(eta d*s (d-1)))) *
          (K^(d-1)*((d-1).factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f (d-1) := by
  have h := actual_weighted_proper_drift_retained_pair_le hμ hf s theta hK hs htheta1 N hprevious
  have hp := Finset.sum_le_sum (s := Finset.Icc 3 N) (fun d hd =>
    mul_le_mul_of_nonneg_left
      (actual_pair_weighted_young_degree hμ hf hK
        (mul_pos (heta d (Finset.mem_Icc.mp hd).1)
          (hs (d-1) (by have := (Finset.mem_Icc.mp hd).1; omega)))
        d (Finset.mem_Icc.mp hd).1)
      (htheta0 d (Finset.mem_Icc.mp hd).1))
  have he : (∑ d ∈ Finset.Icc 3 N, theta d *
      (2*(K^d*(d.factorial : ℝ)^2)⁻¹ *
        (actualAppellCoefficient μ f d ⬝ᵥ actualAppellPairContractionSum μ f d))) =
      2*(∑ d ∈ Finset.Icc 3 N, theta d*(K^d*(d.factorial : ℝ)^2)⁻¹ *
        (actualAppellCoefficient μ f d ⬝ᵥ actualAppellPairContractionSum μ f d)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [he] at hp
  have hr : (∑ d ∈ Finset.Icc 3 N, theta d *
      ((eta d*s (d-1))*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d +
        (((d : ℝ)-1)*((d : ℝ)-1/3)/(K*(eta d*s (d-1)))) *
          (K^(d-1)*((d-1).factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f (d-1))) =
      (∑ d ∈ Finset.Icc 3 N, theta d*eta d*s (d-1) *
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) +
      ∑ d ∈ Finset.Icc 3 N,
        (theta d*((d : ℝ)-1)*((d : ℝ)-1/3)/(K*(eta d*s (d-1)))) *
          (K^(d-1)*((d-1).factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f (d-1) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [hr] at hp
  have hfirst : (∑ d ∈ Finset.Icc 3 N,
      (triangleDegreePrefix s d-theta d*(2-theta d-eta d)*s (d-1)) *
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) =
      (∑ d ∈ Finset.Icc 3 N, thetaDegreePrefix s theta d *
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) +
      ∑ d ∈ Finset.Icc 3 N, theta d*eta d*s (d-1) *
        (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [thetaDegreePrefix_eq s theta (Finset.mem_Icc.mp hd).1]
    unfold triangleDegreePrefix
    ring
  rw [hfirst]
  linarith

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_weighted_proper_drift_retained_pair_le
#print axioms KLS.DeterministicBridgeNext.actual_weighted_proper_drift_theta_young_le

import ActualSelectedRowsAppellDrift
import SelectedRowsBoundaryTriangleYoung

/-! The actual same-law/test selected drift estimate includes the exact
boundary lambda=1 only where the selected profile is zero. It uses the
unchanged full preceding joint budget, including all higher rows. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem actual_weighted_selected_rows_remainder_boundary_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {K C : ℝ} (s : ℕ → ℝ) (rho lambda : ℕ → ℕ → ℝ)
    (hK : 0 < K) (hs : ∀ b, 2 ≤ b → 0 < s b)
    (hrho : ∀ d a, 3 ≤ d → 0 ≤ rho d a)
    (hlambda : ∀ a b, 2 ≤ a → 2 ≤ b → lambda a b ≤ 1)
    (hboundary : ∀ d a, 3 ≤ d → a ∈ Finset.Icc 2 (d-1) →
      lambda a (d-a+1) = 1 → rho d a = 0) (N : ℕ)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x, (g x)^2 ∂μ)) :
    2*(∑ d ∈ Finset.Icc 3 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualProfileProperRemainder μ f rho d)) +
      (∑ p ∈ coupledDriftPairs N, (lambda p.2 (p.1-p.2+1)*K/s (p.1-p.2+1)) *
        (coupledAppellQ μ f K p.2 (p.1-p.2+1))^2) ≤
      (∑ d ∈ Finset.Icc 3 N, selectedRowsPrefix s rho lambda d *
        (K^d*(d.factorial : ℝ)^2)⁻¹ * actualAppellEnergy μ f d) +
      ∑ b ∈ Finset.Icc 2 N, (K*C/s b)*(b : ℝ)^2 *
        (K^b*(b.factorial : ℝ)^2)⁻¹ * actualAppellEnergy μ f b := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hper (d : ℕ) (hd : d ∈ Finset.Icc 3 N) :
      (K^d*(d.factorial : ℝ)^2)⁻¹ *
        (actualAppellCoefficient μ f d ⬝ᵥ actualProfileProperRemainder μ f rho d) ≤
      Real.sqrt K*(∑ a ∈ Finset.Icc 2 (d-1), rho d a *
        (coupledAppellP μ f K d/(d : ℝ))*coupledAppellQ μ f K a (d-a+1)) := by
    have hh := mul_le_mul_of_nonneg_left
      (actual_profile_pairing_le_canonical_sum hμ.logConcave hf rho d
        (fun a => hrho d a (Finset.mem_Icc.mp hd).1))
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
          _ = rho d a *
              ((K^d*(d.factorial : ℝ)^2)⁻¹ * Real.sqrt (actualAppellEnergy μ f d) *
                ((d.choose a : ℝ)*Real.sqrt (actualCanonicalContractionSquare μ f a (d-a)))) := by ring
          _ = _ := by rw [he]; ring
  have hsum := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper)
    (by norm_num : (0 : ℝ) ≤ 2)
  rw [←Finset.mul_sum] at hsum
  have hy := coupled_triangle_selected_rows_young_boundary N (coupledAppellP μ f K)
    (coupledAppellQ μ f K) s rho lambda hK.le hs hlambda hboundary
    (fun b hb => coupledAppellQ_joint_square_le hμ f hK N hprevious hb)
  have hfirst : (∑ d ∈ Finset.Icc 3 N, selectedRowsPrefix s rho lambda d *
      (coupledAppellP μ f K d/(d : ℝ))^2) =
      ∑ d ∈ Finset.Icc 3 N, selectedRowsPrefix s rho lambda d *
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
  change _ + (∑ p ∈ coupledDriftPairs N, (lambda p.2 (p.1-p.2+1)*K/s (p.1-p.2+1)) *
        (coupledAppellQ μ f K p.2 (p.1-p.2+1))^2) ≤ _ at hy
  have hsum' : 2*(∑ d ∈ Finset.Icc 3 N, (K^d*(d.factorial : ℝ)^2)⁻¹ *
      (actualAppellCoefficient μ f d ⬝ᵥ actualProfileProperRemainder μ f rho d)) ≤
      2*Real.sqrt K * (∑ d ∈ Finset.Icc 3 N,
        ∑ a ∈ Finset.Icc 2 (d-1), rho d a *
          (coupledAppellP μ f K d/(d : ℝ))*coupledAppellQ μ f K a (d-a+1)) := by
    convert hsum using 1; ring
  linarith

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_weighted_selected_rows_remainder_boundary_le

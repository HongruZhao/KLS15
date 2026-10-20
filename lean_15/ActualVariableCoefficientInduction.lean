import ActualVariableCoefficientInductionStep
import ActualAppellCoefficientInduction

/-! Genuine all-order coefficient bounds from scalar barriers with a
pointwise generator parameter. The original law class and test class are
unchanged; only scalar barrier data are supplied. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped Topology BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

 theorem actualAppellEnergy_all_variable_coefficient_bounds {n : ℕ} {h : ℕ → ℝ}
    (hh : ∀ d : ℕ, 0 < h d) (h1 : (1:ℝ)≤h 1) (h2 : (8:ℝ)≤h 2)
    (hbarrier : ∀ k : ℕ, 2≤k → Nonempty (VariableCoefficientInductionBarrier k h)) :
    ∀ d : ℕ, 1≤d → ∀ (μ : Measure (Space n)), admissibleMeasure μ →
      ∀ f : Space n → ℝ, MemLp f 2 μ → actualAppellEnergy μ f d≤h d*(∫ x, (f x)^2 ∂μ) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd μ hμ f hf
    letI : IsProbabilityMeasure μ := hμ.isProb
    have hi : 0≤∫ x, (f x)^2 ∂μ := integral_nonneg fun x => sq_nonneg _
    by_cases hd1 : d=1
    · subst d
      have hb := actualAppellEnergy_one_le_integral hμ hf
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) hi]
    by_cases hd2 : d=2
    · subst d
      have hb := actualAppellEnergy_two_le_eight_integral hμ hf
      nlinarith [mul_nonneg (sub_nonneg.mpr h2) hi]
    let k := d-1
    have hk : 2≤k := by dsimp [k]; omega
    have hkd : k+1=d := by dsimp [k]; omega
    let μ₀ : ProbabilityMeasure (Space n) := ⟨μ,hμ.isProb⟩
    obtain ⟨b⟩ := hbarrier k hk
    have hprevious : ∀ r : ℕ, 1≤r → r≤k → ∀ (ν : Measure (Space n)), admissibleMeasure ν →
        ∀ g : Space n → ℝ, MemLp g 2 ν → actualAppellEnergy ν g r≤h r*(∫ x, (g x)^2 ∂ν) := by
      intro r hr hrk
      exact ih r (by omega) hr
    have hb := actual_variable_coefficient_induction_step (μ₀ := μ₀) hμ hk
      (fun r _ _ => hh r) hprevious b μ hμ f hf
    simpa only [hkd] using hb

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actualAppellEnergy_all_variable_coefficient_bounds

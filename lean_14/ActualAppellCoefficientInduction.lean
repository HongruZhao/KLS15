import ActualCoefficientInductionStep
import ActualAppellQuadraticSeed

/-! Unconditional all-degree Appell coefficient bounds for the original
isotropic log-concave law class. The lower-degree bounds, genuine joint
maximum, both variations and the scalar excess contradiction are internal. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace Set
open scoped Topology BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

 theorem coefficientH_one_ge_one : (1 : ℝ) ≤ Quintic24886.coefficientH 1 := by
  norm_num [Quintic24886.coefficientH,Quintic24886.exceptionalWeight,
    Quintic24886.C,Quintic24886.B,Quintic24886.K]

 theorem actualAppellEnergy_one_le_integral {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    actualAppellEnergy μ f 1 ≤ ∫ x, (f x)^2 ∂μ := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  rw [actualAppellEnergy_eq_toLp_norm_sq hf]
  calc
    _ ≤ ‖hf.toLp f‖^2 := fullClassAppellTensor_one_norm_sq_le hμ.logConcave hμ.isotropic _
    _ = _ := by
      rw [actualLp_norm_sq_eq_integral]
      exact integral_congr_ae (hf.coeFn_toLp.fun_comp (fun t : ℝ => t^2))

 theorem actualAppellEnergy_all_coefficientH_bounds {n : ℕ} :
    ∀ d : ℕ, 1 ≤ d → ∀ (μ : Measure (Space n)), admissibleMeasure μ →
      ∀ f : Space n → ℝ, MemLp f 2 μ →
      actualAppellEnergy μ f d ≤ Quintic24886.coefficientH d*(∫ x, (f x)^2 ∂μ) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd μ hμ f hf
    letI : IsProbabilityMeasure μ := hμ.isProb
    by_cases hd1 : d = 1
    · subst d
      have hb := actualAppellEnergy_one_le_integral hμ hf
      have hi : 0 ≤ ∫ x, (f x)^2 ∂μ := integral_nonneg fun x => sq_nonneg _
      nlinarith [mul_nonneg (sub_nonneg.mpr coefficientH_one_ge_one) hi]
    by_cases hd2 : d = 2
    · subst d
      rw [Quintic24886.coefficientH_two]
      exact actualAppellEnergy_two_le_eight_integral hμ hf
    have hd3 : 3 ≤ d := by omega
    let k := d-1
    have hk : 2 ≤ k := by dsimp [k]; omega
    have hkd : k+1=d := by dsimp [k]; omega
    let μ₀ : ProbabilityMeasure (Space n) := ⟨μ,hμ.isProb⟩
    obtain ⟨b⟩ := exists_coefficientInductionBarrier hk
    have hprevious : ∀ r : ℕ, 1 ≤ r → r ≤ k → ∀ (ν : Measure (Space n)), admissibleMeasure ν →
        ∀ g : Space n → ℝ, MemLp g 2 ν →
        actualAppellEnergy ν g r ≤ Quintic24886.coefficientH r*(∫ x, (g x)^2 ∂ν) := by
      intro r hr hrk
      exact ih r (by omega) hr
    have hb := actual_coefficient_induction_step (μ₀ := μ₀) hμ hk
      (fun r _ _ => Quintic24886.coefficientH_positive r) hprevious b μ hμ f hf
    simpa only [hkd] using hb

 theorem actualAppellEnergy_coefficientH_bound {n d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    actualAppellEnergy μ f d ≤ Quintic24886.coefficientH d*(∫ x, (f x)^2 ∂μ) :=
  actualAppellEnergy_all_coefficientH_bounds d hd μ hμ f hf

 theorem actualAppellEnergy_factorial_geometric_bound {n d : ℕ} (hd : 3 ≤ d)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    actualAppellEnergy μ f d ≤
      (121/4 : ℝ)*(2221/100 : ℝ)^(d-3)*(Nat.factorial d : ℝ)^2*(∫ x, (f x)^2 ∂μ) := by
  have hb := actualAppellEnergy_coefficientH_bound (by omega : 1 ≤ d) hμ hf
  rw [Quintic24886.coefficientH_ge_three hd] at hb
  simpa only [Quintic24886.B,Quintic24886.K] using hb

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actualAppellEnergy_all_coefficientH_bounds
#print axioms KLS.DeterministicBridgeNext.actualAppellEnergy_factorial_geometric_bound

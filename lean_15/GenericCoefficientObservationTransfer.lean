import GenericVariableBarrierAssembly
import ActualCoefficientObservationBounds
import VariableAlpha24Numerics

/-! Genuine all-order Appell bounds and the actual graded observation envelope
for an arbitrary positive factorial/geometric scheme. -/
noncomputable section
open MeasureTheory Matrix Set
open scoped ContDiff ENNReal
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

 theorem actualAppellEnergy_factorial_scheme_bound {n : ℕ} (s : FactorialScheme)
    (hBK : s.K ≤ s.B)
    (hseed : Nonempty (VariableCoefficientInductionBarrier 2 s.coefficientH))
    (hcommon : ∀ k : ℕ, 3 ≤ k → Nonempty (VariableCoefficientInductionBarrier k s.coefficientH))
    {d : ℕ} (hd : 1 ≤ d) {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    actualAppellEnergy μ f d ≤ s.coefficientH d*(∫ x,(f x)^2 ∂μ) := by
  have h1 : (1:ℝ) ≤ s.coefficientH 1 := by
    rw [FactorialScheme.coefficientH_one]
    exact (le_div_iff₀ s.K_positive).mpr (by simpa using hBK)
  have h2 : (8:ℝ) ≤ s.coefficientH 2 := by rw [FactorialScheme.coefficientH_two]
  apply actualAppellEnergy_all_variable_coefficient_bounds
    (fun d => FactorialScheme.coefficientH_positive d) h1 h2 ?_ d hd μ hμ f hf
  intro k hk
  by_cases hkeq : k=2
  · simpa only [hkeq] using hseed
  · exact hcommon k (by omega)

 variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0<κ)
  (hlower : ∀ x (a : Fin n → ℝ),
    κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

 theorem actual_observation_factorial_envelope (s : FactorialScheme)
    (hμ : admissibleMeasure (potentialMeasure φ))
    (hcoeff : ∀ j (f : Lp ℝ 2 (potentialMeasure φ)),
      actualAppellEnergy (potentialMeasure φ) f (j+3) ≤ s.coefficientH (j+3)*‖f‖^2)
    (j : ℕ) :
    ‖((gradedTensorIntegration hφ hκ hlower)^(j+2)).comp
      (gradedConstantIntegration hφ hκ hlower hμ.isotropic)‖^2 ≤ s.B*s.K^j := by
  have he := actual_repeated_observation_sq_le_of_energy hφ hκ hlower hμ (j+2)
    (FactorialScheme.coefficientH_positive (s:=s) (j+3)).le (hcoeff j)
  have hfac : ((j+3).factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (j+3)
  rw [FactorialScheme.coefficientH_ge_three (by omega : 3 ≤ j+3)] at he
  have hid : ((j+2+1).factorial : ℝ)⁻¹^2*
      (s.B*s.K^(j+3-3)*((j+3).factorial : ℝ)^2)=s.B*s.K^j := by
    simp only [show j+2+1=j+3 by omega,show j+3-3=j by omega]
    field_simp
  exact hid ▸ he

 theorem actual_observation_factorial_envelope_of_scalar_barriers (s : FactorialScheme)
    (hBK : s.K ≤ s.B)
    (hseed : Nonempty (VariableCoefficientInductionBarrier 2 s.coefficientH))
    (hcommon : ∀ k : ℕ, 3 ≤ k → Nonempty (VariableCoefficientInductionBarrier k s.coefficientH))
    (hμ : admissibleMeasure (potentialMeasure φ)) (j : ℕ) :
    ‖((gradedTensorIntegration hφ hκ hlower)^(j+2)).comp
      (gradedConstantIntegration hφ hκ hlower hμ.isotropic)‖^2 ≤ s.B*s.K^j := by
  apply actual_observation_factorial_envelope hφ hκ hlower s hμ ?_ j
  intro l f
  have hb := actualAppellEnergy_factorial_scheme_bound s hBK hseed hcommon
    (by omega : 1 ≤ l+3) hμ (Lp.memLp f)
  rwa [←actualLp_norm_sq_eq_integral] at hb

end KLS.DeterministicBridgeNext

namespace VariableAlpha24
open KLS.DeterministicBridgeNext

def scheme : FactorialScheme := FactorialScheme.of_pos B K B_positive K_positive
@[simp] theorem scheme_B : scheme.B=B := rfl
@[simp] theorem scheme_K : scheme.K=K := rfl
 theorem scheme_delta : scheme.delta=delta := by
  norm_num [scheme,FactorialScheme.of_pos,FactorialScheme.delta,FactorialScheme.C,delta,B,K]
 theorem scheme_delta_lt : scheme.delta<1/2 := by rw [scheme_delta]; exact delta_range.2
 theorem scheme_K_le_B : scheme.K ≤ scheme.B := by norm_num [scheme,B,K,FactorialScheme.of_pos]
 theorem scheme_r : scheme.r=Real.sqrt B/K := rfl

end VariableAlpha24
#print axioms KLS.DeterministicBridgeNext.actualAppellEnergy_factorial_scheme_bound
#print axioms KLS.DeterministicBridgeNext.actual_observation_factorial_envelope
#print axioms KLS.DeterministicBridgeNext.actual_observation_factorial_envelope_of_scalar_barriers

import KLSConstantImprovement.GeneralWeightedObservation

/-! A positive uniform weight floor is not required for the actual power
envelope. A positive floor after every exponential rescaling suffices.
The same all-test raw budget is preserved exactly by the rescaling. -/
noncomputable section
open MeasureTheory Matrix ContinuousLinearMap
open scoped ContDiff BigOperators ENNReal
namespace KLSConstantImprovement.GeneralSubexponentialWeightedObservation
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.GeneralWeightedObservation
set_option maxHeartbeats 110000000
set_option synthInstance.maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

def SubexponentialLowerWeight (t : ℕ → ℝ) : Prop :=
  ∀ ρ : ℝ,1 < ρ → ∃ τ : ℝ,0 < τ ∧ ∀ d,2 ≤ d → τ ≤ t d*ρ^d

theorem rescaled_coefficient (t K ρ : ℝ) (d : ℕ) (hρ : ρ≠0) :
    (t*ρ^d)*(K*ρ)⁻¹^d=t*K⁻¹^d := by
  rw [_root_.mul_inv_rev,mul_pow]
  calc
    (t*ρ^d)*(ρ⁻¹^d*K⁻¹^d)=t*K⁻¹^d*(ρ^d*ρ⁻¹^d) := by ring
    _=t*K⁻¹^d := by rw [←mul_pow,mul_inv_cancel₀ hρ,one_pow,mul_one]

variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (v : Fin n → ℝ),
    κ*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ x *ᵥ v))
  (hμ : admissibleMeasure (potentialMeasure φ))

include hμ in
/-- The actual graded inverse-gradient adjoint has the same all-rate
envelope under any weights whose reciprocals grow subexponentially. -/
theorem actual_subexponential_adjoint_power_envelope {K C : ℝ}
    (hK : 0 < K) (hC : 0 ≤ C) (t : ℕ → ℝ)
    (ht : SubexponentialLowerWeight t)
    (hraw : ∀ (N : ℕ) (f : Lp ℝ 2 (potentialMeasure φ)),
      (∑ d∈Finset.Icc 2 N,t d*K⁻¹^d*actualAppellEnergy
        (potentialMeasure φ) f d/(d.factorial : ℝ)^2) ≤ C*‖f‖^2) :
    ∀ q : ℝ,1 < q → ∃ M : ℝ,∀ m,
      ‖(gradedTensorIntegration hφ hκ hlower).adjoint^m‖^2 ≤ M*(K*q)^m := by
  intro q hq
  let ρ : ℝ := (q+1)/2
  have hρ1 : 1 < ρ := by dsimp only [ρ]; linarith
  have hρq : ρ < q := by dsimp only [ρ]; linarith
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨τ,hτ,hfloor⟩ := ht ρ hρ1
  have hbudget : ∀ (N : ℕ) (f : Lp ℝ 2 (potentialMeasure φ)),
      (∑ d∈Finset.Icc 2 N,(t d*ρ^d)*(K*ρ)⁻¹^d*actualAppellEnergy
        (potentialMeasure φ) f d/(d.factorial : ℝ)^2) ≤ C*‖f‖^2 := by
    intro N f
    calc
      _=(∑ d∈Finset.Icc 2 N,t d*K⁻¹^d*actualAppellEnergy
          (potentialMeasure φ) f d/(d.factorial : ℝ)^2) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [rescaled_coefficient (t d) K ρ d (ne_of_gt hρ0)]
      _ ≤ _ := hraw N f
  have hη : 1 < q/ρ := (lt_div_iff₀ hρ0).mpr (by simpa using hρq)
  obtain ⟨M,hM⟩ := actual_general_adjoint_power_envelope hφ hκ hlower hμ
    (mul_pos hK hρ0) hC hτ (fun d=>t d*ρ^d) hfloor hbudget (q/ρ) hη
  have he : (K*ρ)*(q/ρ)=K*q := by
    field_simp [ne_of_gt hρ0] <;> ring
  refine ⟨M,fun m=>?_⟩
  simpa only [he] using hM m

end KLSConstantImprovement.GeneralSubexponentialWeightedObservation
#print axioms KLSConstantImprovement.GeneralSubexponentialWeightedObservation.rescaled_coefficient
#print axioms KLSConstantImprovement.GeneralSubexponentialWeightedObservation.actual_subexponential_adjoint_power_envelope

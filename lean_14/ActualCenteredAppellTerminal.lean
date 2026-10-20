import ActualCenteredWeightedAppellHeat
import ActualExactTriangleAppellDrift

/-! The exact terminal pairing and its cancellation with the centered heat gain. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem actual_weighted_terminal_eq
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (K : ℝ) (N : ℕ)
    (hstat : ∀ ell : Lp ℝ 2 μ,actualWeightedAppellPairing f ell K N=
      actualWeightedAppellEnergy μ f K N*inner ℝ f ell) :
    (∑ d∈Finset.Icc 2 N,(K^d*(d.factorial : ℝ)^2)⁻¹*
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellCoefficient μ
        (fun x => inner ℝ x (affineProjectionVector hμ.isotropic f)) d)) =
      actualWeightedAppellEnergy μ f K N*actualAppellEnergy μ f 1 := by
  have hs := hstat (isotropicLinearObservable hμ.isotropic (affineProjectionVector hμ.isotropic f))
  unfold actualWeightedAppellPairing at hs
  simp_rw [fullClassAppellTensor_linear_observable,actualAppell_tensor_inner_array] at hs
  rw [inner_isotropicLinearObservable_projection] at hs
  rw [hs,actualAppellEnergy_eq_norm_sq,
    fullClassAppellTensor_one_norm_sq hμ.logConcave hμ.isotropic]

theorem actual_weighted_centered_full_drift_exact_triangle_le
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) {K C s : ℝ}
    (hK : 0<K) (hC : 0≤C) (hs : 0<s) (N : ℕ)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x,(g x)^2 ∂μ))
    (hstat : ∀ ell : Lp ℝ 2 μ,actualWeightedAppellPairing f ell K N=
      actualWeightedAppellEnergy μ f K N*inner ℝ f ell) :
    2*(∑ d∈Finset.Icc 2 N,(K^d*(d.factorial : ℝ)^2)⁻¹*
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d))-
      actualWeightedAppellEnergy μ f K N*actualAppellEnergy μ f 1 ≤
      actualWeightedAppellEnergy μ f K N+
      s*(∑ d∈Finset.Icc 3 N,((d : ℝ)-2)*(K^d*(d.factorial : ℝ)^2)⁻¹*
        actualAppellEnergy μ f d)+
      (K*C/s)*(∑ d∈Finset.Icc 2 N,
        (d : ℝ)^2*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) := by
  have ht := actual_weighted_terminal_eq hμ f K N hstat
  have hb : actualAppellEnergy μ f 1 ≤ 1 := by
    rw [actualAppellEnergy_eq_norm_sq]
    simpa only [hunit,one_pow] using fullClassAppellTensor_one_norm_sq_le hμ.logConcave hμ.isotropic f
  have hM := actualWeightedAppellEnergy_nonneg μ f hK N
  have hMb := mul_le_of_le_one_right hM hb
  have hp := actual_weighted_proper_drift_exact_triangle_le hμ (Lp.memLp f) hK hC hs N hprevious
  rw [actual_weighted_proper_drift_sum_eq f K N] at hp
  have he : (∑ d∈Finset.Icc 2 N,(K^d*(d.factorial : ℝ)^2)⁻¹*
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d)) =
      (∑ d∈Finset.Icc 2 N,(K^d*(d.factorial : ℝ)^2)⁻¹*
        (actualAppellCoefficient μ f d ⬝ᵥ actualAppellCoefficient μ
          (fun x => inner ℝ x (affineProjectionVector hμ.isotropic f)) d))+
      (∑ d∈Finset.Icc 2 N,(K^d*(d.factorial : ℝ)^2)⁻¹*
        (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d)) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [actualAppellLowerDriftTensor_terminal_split hμ.logConcave hμ.isotropic f
      (Finset.mem_Icc.mp hd).1,dotProduct_add]
    ring
  rw [he]
  linarith

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_weighted_terminal_eq
#print axioms KLS.DeterministicBridgeNext.actual_weighted_centered_full_drift_exact_triangle_le

import ActualCoupledAppellDrift
import ActualAppellCombinedTerminal

/-! The actual linear-test cancellation for every terminal cumulant in a
finite coupled energy. Test stationarity is used once for the entire sum. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix
open scoped ContDiff BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem actual_weighted_terminal_le
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) {K : ℝ} (hK : 0 < K) (N : ℕ)
    (hstat : ∀ ell : Lp ℝ 2 μ,
      actualWeightedAppellPairing f ell K N=
        actualWeightedAppellEnergy μ f K N*inner ℝ f ell) :
    (∑ d ∈ Finset.Icc 2 N, (K^d*(d.factorial : ℝ)^2)⁻¹*
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellCoefficient μ
        (fun x => inner ℝ x (affineProjectionVector hμ.isotropic f)) d)) ≤
      actualWeightedAppellEnergy μ f K N := by
  have hs := hstat (isotropicLinearObservable hμ.isotropic (affineProjectionVector hμ.isotropic f))
  unfold actualWeightedAppellPairing at hs
  simp_rw [fullClassAppellTensor_linear_observable,actualAppell_tensor_inner_array] at hs
  rw [inner_isotropicLinearObservable_projection] at hs
  rw [hs]
  have hb : ‖affineProjectionVector hμ.isotropic f‖^2 ≤ 1 := by
    simpa only [hunit,one_pow] using affineProjectionVector_norm_sq_le_full hμ.isotropic f
  exact mul_le_of_le_one_right (actualWeightedAppellEnergy_nonneg μ f hK N) hb

theorem actualAppellProperRemainder_two_zero
    (μ : Measure (Space n)) (f : Space n → ℝ) : actualAppellProperRemainder μ f 2=0 := by
  classical
  funext a
  unfold actualAppellProperRemainder
  simp only [Finset.sum_apply,Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro S hS
  have hn : ¬ (2 ≤ S.card ∧ S.card ≤ 2-1) := by omega
  simp only [hn,ite_false,Pi.zero_apply]

theorem actual_weighted_proper_drift_sum_eq
    {μ : Measure (Space n)} (f : Space n → ℝ) (K : ℝ) (N : ℕ) :
    (∑ d ∈ Finset.Icc 3 N, (K^d*(d.factorial : ℝ)^2)⁻¹*
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d)) =
    (∑ d ∈ Finset.Icc 2 N, (K^d*(d.factorial : ℝ)^2)⁻¹*
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d)) := by
  classical
  apply Finset.sum_subset (by intro d hd; simp only [Finset.mem_Icc] at hd ⊢; omega)
  intro d hd hn
  have hd2 : d=2 := by simp only [Finset.mem_Icc] at hd hn; omega
  subst d
  rw [actualAppellProperRemainder_two_zero]
  simp

/-- All actual cumulant drift terms at a genuine weighted test maximizer.
The previous coupled energy bound supplies every proper contraction;
stationarity supplies every terminal term simultaneously. -/
theorem actual_weighted_full_drift_le
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) {K C : ℝ} (hK : 0 < K) (hC : 0 ≤ C)
    (N : ℕ)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x, (g x)^2 ∂μ))
    (hstat : ∀ ell : Lp ℝ 2 μ,
      actualWeightedAppellPairing f ell K N=
        actualWeightedAppellEnergy μ f K N*inner ℝ f ell) :
    2*(∑ d ∈ Finset.Icc 2 N, (K^d*(d.factorial : ℝ)^2)⁻¹*
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d)) ≤
      2*actualWeightedAppellEnergy μ f K N+
        Real.sqrt (K*C/2)*(∑ d ∈ Finset.Icc 2 N,
          (d : ℝ)^2*(K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) := by
  have ht := actual_weighted_terminal_le hμ f hunit hK N hstat
  have hp := actual_weighted_proper_drift_le hμ (Lp.memLp f) hK hC N hprevious
  rw [actual_weighted_proper_drift_sum_eq f K N] at hp
  have he : (∑ d ∈ Finset.Icc 2 N, (K^d*(d.factorial : ℝ)^2)⁻¹*
      (actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d)) =
      (∑ d ∈ Finset.Icc 2 N, (K^d*(d.factorial : ℝ)^2)⁻¹*
        (actualAppellCoefficient μ f d ⬝ᵥ actualAppellCoefficient μ
          (fun x => inner ℝ x (affineProjectionVector hμ.isotropic f)) d))+
      (∑ d ∈ Finset.Icc 2 N, (K^d*(d.factorial : ℝ)^2)⁻¹*
        (actualAppellCoefficient μ f d ⬝ᵥ actualAppellProperRemainder μ f d)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [actualAppellLowerDriftTensor_terminal_split hμ.logConcave hμ.isotropic f
      (Finset.mem_Icc.mp hd).1, dotProduct_add]
    ring
  rw [he]
  linarith

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_weighted_full_drift_le

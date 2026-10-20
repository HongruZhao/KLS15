import ActualWeightedAppellHeat
import ActualCoupledAppellTerminal

/-! The paper's actual generator, summed with degree-dependent parameters.
Each parameter is only used algebraically at its own degree. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def appellGeneratorLoss (beta : ℕ → ℝ) (d : ℕ) : ℝ := 4/(1-beta d)-2

theorem actual_variable_weighted_generator_sum_lower
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) {K C : ℝ} (hK : 0<K) (hC : 0≤C)
    (N : ℕ) (beta : ℕ → ℝ)
    (hbeta0 : ∀ d∈Finset.Icc 2 N, 0≤beta d)
    (hbeta1 : ∀ d∈Finset.Icc 2 N, beta d<1)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1) ≤ C*(∫ x,(g x)^2 ∂μ))
    (hstat : ∀ ell : Lp ℝ 2 μ, actualWeightedAppellPairing f ell K N=
      actualWeightedAppellEnergy μ f K N*inner ℝ f ell)
    (hheat : actualWeightedAppellHeatGenerator μ f K N≤0) :
    (∑ d∈Finset.Icc 2 N,beta d*(K^d*(d.factorial : ℝ)^2)⁻¹*
      actualAppellEnergy μ f (d+1)) ≤
    (∑ d∈Finset.Icc 2 N,
      ((appellGeneratorLoss beta d+Real.sqrt (K*C/2))*(d : ℝ)^2+
        (appellGeneratorLoss beta d-3)*(d : ℝ)+2)*
      (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) := by
  classical
  let w : ℕ → ℝ := fun d => (K^d*(d.factorial : ℝ)^2)⁻¹
  let R := ∑ d∈Finset.Icc 2 N,w d*
    (actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d)
  let D := ∑ d∈Finset.Icc 2 N,(d : ℝ)^2*w d*actualAppellEnergy μ f d
  let S := ∑ d∈Finset.Icc 2 N,beta d*w d*actualAppellEnergy μ f (d+1)
  let L := ∑ d∈Finset.Icc 2 N,
    (appellGeneratorLoss beta d*(d : ℝ)^2+
      (appellGeneratorLoss beta d-3)*(d : ℝ))*w d*actualAppellEnergy μ f d
  have hw (d : ℕ) : 0≤w d := by
    exact inv_nonneg.mpr (mul_nonneg (pow_nonneg hK.le _) (sq_nonneg _))
  have hlower : S-L-2*R≤actualWeightedAppellHeatGenerator μ f K N := by
    have hh := Finset.sum_le_sum (s:=Finset.Icc 2 N) (fun d hd =>
      mul_le_mul_of_nonneg_left (actualCovarianceAppellEnergy_generator_lower
        hμ (Lp.memLp f) d (hbeta0 d hd) (hbeta1 d hd)) (hw d))
    change (∑ d∈Finset.Icc 2 N,w d*(beta d*actualAppellEnergy μ f (d+1)-
      (appellGeneratorLoss beta d*(d : ℝ)^2+
        (appellGeneratorLoss beta d-3)*(d : ℝ))*actualAppellEnergy μ f d-
      2*(actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d)))≤
        actualWeightedAppellHeatGenerator μ f K N at hh
    have he : S-L-2*R =
        ∑ d∈Finset.Icc 2 N,w d*(beta d*actualAppellEnergy μ f (d+1)-
          (appellGeneratorLoss beta d*(d : ℝ)^2+
            (appellGeneratorLoss beta d-3)*(d : ℝ))*actualAppellEnergy μ f d-
          2*(actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d)) := by
      dsimp only [S,L,R]
      rw [Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    rwa [he]
  have hdrift := actual_weighted_full_drift_le hμ f hunit hK hC N hprevious hstat
  change 2*R≤2*actualWeightedAppellEnergy μ f K N+Real.sqrt (K*C/2)*D at hdrift
  have he : (∑ d∈Finset.Icc 2 N,
      ((appellGeneratorLoss beta d+Real.sqrt (K*C/2))*(d : ℝ)^2+
        (appellGeneratorLoss beta d-3)*(d : ℝ)+2)*
      (K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) =
      L+Real.sqrt (K*C/2)*D+2*actualWeightedAppellEnergy μ f K N := by
    dsimp only [L,D]
    unfold actualWeightedAppellEnergy
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    dsimp only [w]
    ring
  rw [he]
  change S≤_
  linarith

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_variable_weighted_generator_sum_lower

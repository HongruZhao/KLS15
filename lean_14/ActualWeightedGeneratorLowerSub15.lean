import ActualSymmetricQuadraticGeneratorCoefficients
import CoupledSub15Numerics

/-! Concrete genuine centered weighted generator for K=67/5,C=6/125.
Only the already-proved symmetric rank-two improvement is substituted. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
open CoupledEnergy.NumericsSub15
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem actual_weighted_generator_coefficients_nonpos_sub15
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) (N : ℕ) (hN : 2≤N)
    (hprevious : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualWeightedAppellEnergy μ g K (N-1)≤C*(∫ x,(g x)^2 ∂μ))
    (hstat : ∀ ell : Lp ℝ 2 μ, actualWeightedAppellPairing f ell K N=
      actualWeightedAppellEnergy μ f K N*inner ℝ f ell)
    (hheat : actualWeightedAppellHeatGenerator μ f K N+
      actualWeightedAppellEnergy μ f K N*actualAppellEnergy μ f 1≤0) :
    (∑ d∈Finset.Icc 3 N,coefficient d*
      ((K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d))-
      head*((K^2*(Nat.factorial 2 : ℝ)^2)⁻¹*actualAppellEnergy μ f 2)≤0 := by
  have hh := actual_symmetric_quadratic_generator_coefficients_nonpos hμ f hunit
    K_positive C_positive.le young young_positive alpha alpha_nonneg alpha_lt_one
    alpha_two_ge_third N hN hprevious hstat hheat
  have htail : (∑ d∈Finset.Icc 3 N,symmetricQuadraticTailCoefficient K C alpha young d*
      ((K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d))=
      ∑ d∈Finset.Icc 3 N,coefficient d*
        ((K^d*(d.factorial : ℝ)^2)⁻¹*actualAppellEnergy μ f d) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hp : properYoungPrefix young d=youngPrefix d :=
      (youngPrefix_eq_sum d (by have := (Finset.mem_Icc.mp hd).1; omega)).symm
    simp only [symmetricQuadraticTailCoefficient,coefficient,appellGeneratorLoss,A,hp]
  rw [htail] at hh
  exact hh

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_weighted_generator_coefficients_nonpos_sub15

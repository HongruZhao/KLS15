import ActualAppellObservationOperators
import KLS.WeightedEnergyGraph
import KLS.WeightedTiltIntegration
import KLS.WeightedTiltSmooth
import KLS.DirectionalWordAlgebra

/-! Genuine first-order weighted Stein identities and their actual mixed
normalized-Laplace derivatives. Compact spatial tests discharge the boundary
terms. No coefficient recursion is assumed. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {φ ψ : Space n → ℝ}

theorem integral_exp_mul_neg_weightedDerivativeTest
    (hφ : ContDiff ℝ 1 φ) (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) (j : Fin n) (z : Space n) :
    (∫ x, -weightedDerivativeTest φ ψ j x * Real.exp (inner ℝ z x)
      ∂potentialMeasure φ) =
      z j * ∫ x, ψ x * Real.exp (inner ℝ z x) ∂potentialMeasure φ := by
  have hex : ContDiff ℝ 1 (fun x : Space n => Real.exp (inner ℝ z x)) := by
    simpa only [innerSL_apply_apply] using (innerSL ℝ z).contDiff.exp
  have hd (x : Space n) :
      coordinateDerivative (fun y => Real.exp (inner ℝ z y)) j x =
        Real.exp (inner ℝ z x) * z j := by
    rw [coordinateDerivative_eq_gradient,gradient_exp_inner]
    rfl
  have hi := integral_coordinateDerivative_mul_compact_test hφ hex hψ hc j
  simp_rw [hd] at hi
  calc
    _ = -(∫ x, Real.exp (inner ℝ z x) * weightedDerivativeTest φ ψ j x
        ∂potentialMeasure φ) := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only; ring
    _ = ∫ x, Real.exp (inner ℝ z x) * z j * ψ x ∂potentialMeasure φ := hi.symm
    _ = z j * ∫ x, ψ x * Real.exp (inner ℝ z x) ∂potentialMeasure φ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only; ring

theorem weightedDerivativeTest_exponentialTilt_identity
    (hφ : ContDiff ℝ 1 φ) (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) (j : Fin n) (z : Space n) :
    (∫ x, -weightedDerivativeTest φ ψ j x ∂exponentialTilt (potentialMeasure φ) z) =
      z j * ∫ x, ψ x ∂exponentialTilt (potentialMeasure φ) z := by
  change tiltAverage (potentialMeasure φ) (fun x => inner ℝ z x)
      (fun x => -weightedDerivativeTest φ ψ j x) =
    z j * tiltAverage (potentialMeasure φ) (fun x => inner ℝ z x) ψ
  rw [tiltAverage_eq_ratio,tiltAverage_eq_ratio,
    integral_exp_mul_neg_weightedDerivativeTest hφ hψ hc j z]
  ring

theorem actualAppellCoefficient_weightedDerivativeTest {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ y *ᵥ a))
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (j : Fin n) (d : ℕ) (a : Fin (d+1) → Fin n) :
    actualAppellCoefficient (potentialMeasure φ)
      (fun x => -weightedDerivativeTest φ ψ j x) (d+1) a =
      ∑ k : Fin (d+1), (if a k = j then 1 else 0) *
        actualAppellCoefficient (potentialMeasure φ) ψ d
          (fun l => a (k.succAbove l)) := by
  have hψ2 := memLp_of_continuous_hasCompactSupport hφ.continuous hψ.continuous hc
  have hs := contDiff_exponentialTilt_average_of_weighted_memLp hφ hκ hlower hψ2
  have he : (fun z => ∫ x, -weightedDerivativeTest φ ψ j x
      ∂exponentialTilt (potentialMeasure φ) z) =
      fun z => (EuclideanSpace.proj (𝕜 := ℝ) j) z *
        ∫ x, ψ x ∂exponentialTilt (potentialMeasure φ) z := by
    funext z
    exact weightedDerivativeTest_exponentialTilt_identity (hφ.of_le (by norm_num)) hψ hc j z
  unfold actualAppellCoefficient
  rw [he,iteratedFDeriv_linear_mul_zero hs]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  change (EuclideanSpace.single (a k) (1 : ℝ)) j = _
  simp [PiLp.single_apply,eq_comm]

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.integral_exp_mul_neg_weightedDerivativeTest
#print axioms KLS.DeterministicBridgeNext.weightedDerivativeTest_exponentialTilt_identity
#print axioms KLS.DeterministicBridgeNext.actualAppellCoefficient_weightedDerivativeTest

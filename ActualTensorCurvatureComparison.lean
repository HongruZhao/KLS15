import ActualCompactCurvaturePositive
import ActualCompactCurvatureOne
import ActualProjectedDivergenceDensity
import ActualCurvatureQuadraticReduction
import ActualRegularEndpointFromCurvature

/-! The genuine all-rank tensor curvature comparison. Compact curvature
is proved in every rank, actual projected-divergence density is proved,
and quadratic duality then gives the real canonical resolvent comparison.
No compact-curvature, Hodge-domain, core-density, or resolvent gate remains
as a premise. This module also discharges the paper-regular curvature gate. -/
noncomputable section
open MeasureTheory Matrix InnerProductSpace Set
open scoped ContDiff BigOperators RealInnerProductSpace
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {n : ℕ} {φ ψ : Space n → ℝ}
variable [IsProbabilityMeasure (potentialMeasure φ)]

/-- Literal compact equation 5.2 for every tensor rank, with all operator
and finite-curvature realization internal to the proof. -/
theorem compactPotentialDivergenceHilbert_allRanks_curvature
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (r : ℕ) {a : ℝ} (ha : 0 ≤ a)
    (hlower : ∀ (x : Space n) (v : Fin n → ℝ),
      a*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ x *ᵥ v)) :
    ‖compactPotentialTensorLp hφ.continuous hψ hc (r+2)‖^2+
      a*‖compactPotentialTensorLp hφ.continuous hψ hc (r+1)‖^2 ≤
      ‖compactPotentialDivergenceHilbert hφ hψ hc r‖^2 := by
  cases r with
  | zero => exact compactPotentialDivergenceHilbert_rank_zero_curvature hφ hψ hc hlower
  | succ r =>
    cases r with
    | zero => exact compactPotentialDivergenceHilbert_rank_one_curvature hφ hψ hc ha hlower
    | succ r =>
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
        compactPotentialDivergenceHilbert_positive_curvature hφ hψ hc r ha hlower

/-- The actual tensor inverse gradients satisfy the canonical rational
comparison. The only analytic inputs are a genuine smooth strongly
convex potential, its Hessian lower bound, and probability normalization. -/
theorem actual_tensor_curvature_comparison
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ (x : Space n) (v : Fin n → ℝ),
      κ*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ x *ᵥ v)) :
    ActualTensorCurvatureComparison hφ hκ hlower := by
  apply actual_tensor_curvature_comparison_of_compact_estimate_and_density hφ hκ hlower
  · exact actual_compactPotentialDivergence_dense hφ hκ hlower
  · intro ψ hψ hc r
    exact compactPotentialDivergenceHilbert_allRanks_curvature hφ hψ hc r hκ.le hlower

/-- The regular-class curvature gate is proved, rather than assumed by
the universal endpoint. In fact the comparison above needs no Hessian
upper bound or derivative-growth assumption. -/
theorem paperRegularTensorCurvatureGate : PaperRegularTensorCurvatureGate := by
  intro n V κ inst hV hκ hstrong hupper hgrowth hμ
  exact actual_tensor_curvature_comparison hV hκ
    (coordinateHessian_lower_of_strongConvexOn (hV.of_le (by simp)) hstrong)

end KLS.DeterministicBridgeNext
end

#print axioms KLS.DeterministicBridgeNext.compactPotentialDivergenceHilbert_allRanks_curvature
#print axioms KLS.DeterministicBridgeNext.actual_tensor_curvature_comparison
#print axioms KLS.DeterministicBridgeNext.paperRegularTensorCurvatureGate

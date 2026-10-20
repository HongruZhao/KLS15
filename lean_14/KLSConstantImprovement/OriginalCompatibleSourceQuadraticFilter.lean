import Mathlib

/-! Exact scalar-gradient source filtering. Actual original moment-map,
source operator/core and integration-by-parts statements remain analytic
inputs; no higher-gap2, all-law response bound or CP improvement is claimed. -/
noncomputable section
namespace KLSConstantImprovement.OriginalCompatibleSourceQuadraticFilter

theorem skew_symmetric_hessian_pair_zero {n : ℕ}
    (C U : Fin n → Fin n → ℝ)
    (hskew : ∀ i j, C j i = -C i j)
    (hsym : ∀ i j, U j i = U i j) :
    (∑ i, ∑ j, C i j * U i j) = 0 := by
  have hswap : (∑ i, ∑ j, C i j * U i j) =
      ∑ i, ∑ j, C j i * U j i := Finset.sum_comm
  have hneg : (∑ i, ∑ j, C j i * U j i) =
      -(∑ i, ∑ j, C i j * U i j) := by
    calc
      (∑ i, ∑ j, C j i * U j i) =
          ∑ i, ∑ j, (-C i j) * U i j := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [hskew i j, hsym i j]
      _ = -(∑ i, ∑ j, C i j * U i j) := by
        simp only [neg_mul, Finset.sum_neg_distrib]
  linarith

theorem compatible_source_filter {y q aq skew qap : ℝ}
    (hfilter : 2*q-aq = 2*y+skew)
    (hadjoint : aq = qap)
    (hscalar_hessian : skew = 0) :
    6*y = 3*(2*q-qap) := by linarith

theorem retained_connection_curvature {y q qap derivative connection curvature : ℝ}
    (hfilter : 6*y = 3*(2*q-qap))
    (hintertwining : qap = derivative-connection-curvature) :
    6*y = 6*q-3*derivative+3*connection+3*curvature := by linarith

end KLSConstantImprovement.OriginalCompatibleSourceQuadraticFilter
#print axioms KLSConstantImprovement.OriginalCompatibleSourceQuadraticFilter.skew_symmetric_hessian_pair_zero
#print axioms KLSConstantImprovement.OriginalCompatibleSourceQuadraticFilter.compatible_source_filter
#print axioms KLSConstantImprovement.OriginalCompatibleSourceQuadraticFilter.retained_connection_curvature

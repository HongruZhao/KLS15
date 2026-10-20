import Mathlib

/-! Exact consequences of the same regular geometric response chi.
Actual source/ordinary divergence closure, commutator Riesz identity,
and vector-Bochner/target-curvature identifications are analytic inputs.
No universal numerical response bound is asserted. -/
namespace GeometricResponseOrdinaryDivergence

theorem symmetric_metric_energy_eq
    (ms ch d2 sh : ℝ) (hbochner : ms + ch = d2 + sh) :
    ms = d2 + sh - ch := by
  linarith

theorem same_response_signed_commutator_eq
    (i ms ch sh cross c2 d2 : ℝ)
    (hbochner : ms + ch = d2 + sh)
    (hsum : d2 = i + 2 * cross + c2) :
    i = ms + ch - sh - 2 * cross - c2 := by
  linarith

theorem retains_matching_square_and_curvature
    (i ms ch sh cross c2 d2 loss curv : ℝ)
    (hbochner : ms + ch = d2 + sh)
    (hsum : d2 = i + 2 * cross + c2)
    (hcompletion : i = ms - loss - curv) :
    ch + loss + curv = 2 * cross + c2 + sh := by
  linarith

end GeometricResponseOrdinaryDivergence

#print axioms GeometricResponseOrdinaryDivergence.symmetric_metric_energy_eq
#print axioms GeometricResponseOrdinaryDivergence.same_response_signed_commutator_eq
#print axioms GeometricResponseOrdinaryDivergence.retains_matching_square_and_curvature

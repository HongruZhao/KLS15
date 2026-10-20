import CorrelatedCubicInitialization
import CorrelatedCubicRationalTangents239

/-! The first-two-observation correlation also improves the third orbit
initialization.  A tangent of the concave seed gives a quadratic lower
bound whose minimum is an exact completed square. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Set
namespace KLSBelow25.CorrelatedInitialization239
open KLS.DeterministicBridgeNext CreationSeed239

def tangentLower (p a b u : ℝ) : ℝ :=
  p^3-b*(seedPhi u-u*deriv seedPhi u)-
    p*(-2*p-(b/a)*deriv seedPhi u)^2/4

theorem correlated_seed_initialization_lower {p a b x y u : ℝ}
    (hp : 0 < p) (ha : 0 < a) (hb : 0 ≤ b)
    (hu : u ∈ Icc (0 : ℝ) 1) (hx : x/a ∈ Icc (0 : ℝ) 1)
    (hy : y ≤ b*seedPhi (x/a)) :
    tangentLower p a b u ≤ (p^2-x)*(p-x/p)-y := by
  have ht := concave_barrier_tangent seedInverseBarrier.concaveOn_phi hu hx
    ((hasDerivAt_seedPhi hu).differentiableAt.hasDerivAt)
  change seedPhi (x/a) ≤ seedPhi u+deriv seedPhi u*(x/a-u) at ht
  exact CorrelatedInitialization.quadratic_initialization_lower hp ha
    (hy.trans (mul_le_mul_of_nonneg_left ht hb))

end KLSBelow25.CorrelatedInitialization239
#print axioms KLSBelow25.CorrelatedInitialization239.correlated_seed_initialization_lower

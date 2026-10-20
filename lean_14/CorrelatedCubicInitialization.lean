import CorrelatedCubicRationalTangents

/-! The first-two-observation correlation also improves the third orbit
initialization.  A tangent of the concave seed gives a quadratic lower
bound whose minimum is an exact completed square. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Set
namespace KLSBelow25.CorrelatedInitialization
open KLS.DeterministicBridgeNext CreationSeed24

def tangentLower (p a b u : ℝ) : ℝ :=
  p^3-b*(seedPhi u-u*deriv seedPhi u)-
    p*(-2*p-(b/a)*deriv seedPhi u)^2/4

theorem quadratic_initialization_lower {p a b x y u F d : ℝ}
    (hp : 0 < p) (ha : 0 < a)
    (hy : y ≤ b*(F+d*(x/a-u))) :
    p^3-b*(F-u*d)-p*(-2*p-(b/a)*d)^2/4 ≤
      (p^2-x)*(p-x/p)-y := by
  let D := -2*p-(b/a)*d
  let lower := p^3-b*(F-u*d)-p*D^2/4
  have he : (p^2-x)*(p-x/p)-b*(F+d*(x/a-u)) =
      lower+(x+p*D/2)^2/p := by
    dsimp [lower, D]
    field_simp [hp.ne', ha.ne']
    ring
  change lower ≤ _
  calc
    lower ≤ lower+(x+p*D/2)^2/p :=
      le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hp.le)
    _ = (p^2-x)*(p-x/p)-b*(F+d*(x/a-u)) := he.symm
    _ ≤ (p^2-x)*(p-x/p)-y := sub_le_sub_left hy _

theorem correlated_seed_initialization_lower {p a b x y u : ℝ}
    (hp : 0 < p) (ha : 0 < a) (hb : 0 ≤ b)
    (hu : u ∈ Icc (0 : ℝ) 1) (hx : x/a ∈ Icc (0 : ℝ) 1)
    (hy : y ≤ b*seedPhi (x/a)) :
    tangentLower p a b u ≤ (p^2-x)*(p-x/p)-y := by
  have ht := concave_barrier_tangent seedInverseBarrier.concaveOn_phi hu hx
    ((hasDerivAt_seedPhi hu).differentiableAt.hasDerivAt)
  change seedPhi (x/a) ≤ seedPhi u+deriv seedPhi u*(x/a-u) at ht
  exact quadratic_initialization_lower hp ha
    (hy.trans (mul_le_mul_of_nonneg_left ht hb))

end KLSBelow25.CorrelatedInitialization
#print axioms KLSBelow25.CorrelatedInitialization.quadratic_initialization_lower
#print axioms KLSBelow25.CorrelatedInitialization.correlated_seed_initialization_lower

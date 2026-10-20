import Mathlib

/-! Finite scalar consequences for the actual regular-source weighted Gamma
domain proof. Source construction, generator identities, pullback cutoffs,
Fatou and all measure identifications are paper inputs, not formalized here.
These dimension-dependent domain bounds do not imply a universal response
or Poincare improvement. -/
namespace KLSConstantImprovement.FullSupportWeightedSourceGammaDomainScalar

theorem signed_cross_young_lower {u s c : ℝ}
    (hs : 0 ≤ s) (hc : 0 ≤ c) (hu : u^2 ≤ c*s) :
    -s/2-8*c ≤ 4*u := by
  have hsq : (-4*u)^2 ≤ (s/2+8*c)^2 := by
    nlinarith [sq_nonneg (s/2-8*c)]
  have hp : 0 ≤ s/2+8*c := by positivity
  have hl := le_of_sq_le_sq hsq hp
  linarith

theorem positive_generator_lower {LF F h p s u c : ℝ}
    (hp : 0 ≤ p) (hs : 0 ≤ s) (hc : 0 ≤ c)
    (hu : u^2 ≤ c*s)
    (hgen : LF+3*F=2*h^2+p+s+4*u) :
    s/2+p ≤ LF+3*F+8*c := by
  have hy := signed_cross_young_lower hs hc hu
  nlinarith [sq_nonneg h]

theorem integrated_weighted_gamma_budget {EF EG W c : ℝ}
    (hG : EG=3*EF+8*c) (hW : W/2 ≤ EG) :
    W ≤ 6*EF+16*c := by linarith

theorem isotropic_fixed_law_domain_budget {W EF n M : ℝ}
    (hW : W ≤ 6*EF+16*n*M^2) (hF : EF ≤ M*n^2) :
    W ≤ 6*M*n^2+16*n*M^2 := by linarith

end KLSConstantImprovement.FullSupportWeightedSourceGammaDomainScalar

#print axioms KLSConstantImprovement.FullSupportWeightedSourceGammaDomainScalar.signed_cross_young_lower
#print axioms KLSConstantImprovement.FullSupportWeightedSourceGammaDomainScalar.positive_generator_lower
#print axioms KLSConstantImprovement.FullSupportWeightedSourceGammaDomainScalar.integrated_weighted_gamma_budget
#print axioms KLSConstantImprovement.FullSupportWeightedSourceGammaDomainScalar.isotropic_fixed_law_domain_budget

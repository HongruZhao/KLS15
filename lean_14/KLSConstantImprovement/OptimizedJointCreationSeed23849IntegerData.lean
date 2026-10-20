import KLSConstantImprovement.OptimizedJointCreationSeed23849IntegerHead
import KLSConstantImprovement.OptimizedJointCreationSeed23849IntegerDetLow
import KLSConstantImprovement.OptimizedJointCreationSeed23849IntegerDetCap
noncomputable section
open Set
namespace KLSBelow25.OptimizedJointCreationSeed23849
open KLSBelow25.BernsteinInterval
theorem seedNegQ_formula (t:ℝ) : seedNegQ t=((214641/2000)*seedC+64/(3*seedC))*t*seedV t+seedRAt t*t*(seedV t)^2*seedSlope t := by
  by_cases h:t ≤ seedSwitch <;> simp [seedNegQ,seedRAt,h,seedNegQLow,seedNegQCap]
theorem seedDet_positive {t:ℝ} (ht:t∈Icc 0 seedT) : 0<seedDet t := by
  by_cases h:t ≤ seedSwitch
  · have hp:=seedDetLow_positive ⟨ht.1,h⟩
    simpa only [seedDet,seedNegQ,h,ite_true,seedDetLow] using hp
  · have hp:=seedDetCap_positive ⟨(lt_of_not_ge h).le,ht.2⟩
    simpa only [seedDet,seedNegQ,h,ite_false,seedDetCap] using hp
theorem seedNegQ_positive {t:ℝ} (ht:0<t) (htT:t ≤ seedT) : 0<seedNegQ t := by
  have hv:=seedV_positive ⟨ht.le,htT⟩
  have hs:=seedSlope_positive ⟨ht.le,htT⟩
  have hc:=seedC_positive
  have hr:=seedRAt_positive t
  rw [seedNegQ_formula]
  positivity
end KLSBelow25.OptimizedJointCreationSeed23849
#print axioms KLSBelow25.OptimizedJointCreationSeed23849.seedV_positive
#print axioms KLSBelow25.OptimizedJointCreationSeed23849.seedSlope_positive
#print axioms KLSBelow25.OptimizedJointCreationSeed23849.seedConcavity_positive
#print axioms KLSBelow25.OptimizedJointCreationSeed23849.seedP_positive
#print axioms KLSBelow25.OptimizedJointCreationSeed23849.seedDetLow_positive
#print axioms KLSBelow25.OptimizedJointCreationSeed23849.seedDetCap_positive
#print axioms KLSBelow25.OptimizedJointCreationSeed23849.seedDet_positive
#print axioms KLSBelow25.OptimizedJointCreationSeed23849.seedAlphaPoly_positive
#print axioms KLSBelow25.OptimizedJointCreationSeed23849.seed_zero_strict_margin
#print axioms KLSBelow25.OptimizedJointCreationSeed23849.seed_endpoint_above_one
#print axioms KLSBelow25.OptimizedJointCreationSeed23849.seedR_domination
#print axioms KLSBelow25.OptimizedJointCreationSeed23849.seedRLow_difference
#print axioms KLSBelow25.OptimizedJointCreationSeed23849.seedRLow_domination
#print axioms KLSBelow25.OptimizedJointCreationSeed23849.seedRAt_positive
#print axioms KLSBelow25.OptimizedJointCreationSeed23849.seedRootMargin_positive
#print axioms KLSBelow25.OptimizedJointCreationSeed23849.seedRLow_floor_positive

import KLSConstantImprovement.AffineSameTestCreationSeed238452IntegerDetNewHorner
import KLSConstantImprovement.AffineSameTestCreationSeed238452IntegerDetCapHorner
noncomputable section
open Set
namespace KLSBelow25.AffineSameTestCreationSeed238452
open KLSBelow25.BernsteinInterval
open KLSConstantImprovement.IntegerListPolynomialCertificate
open KLSConstantImprovement.IntegerHornerBernsteinCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem seedNegQ_formula (t : ℝ) : seedNegQ t=((536517/5000)*seedC+64/(3*seedC))*t*seedV t+seedRAt t*t*(seedV t)^2*seedSlope t := rfl
theorem seedP_formula (t : ℝ) : seedP t=(536517/5000)*(1-t^2)+17*t^2*(seedV t)^2-(16+seedExtraAt t*t^2*(seedV t)^2)*(1-t^2)*seedV t*seedSlope t := by
  by_cases h : t ≤ seedCut
  · simp only [seedP,seedExtraAt,h,ite_true,seedPNew,seedPCap]; ring
  · simp only [seedP,seedExtraAt,h,ite_false,seedPCap]; ring
theorem seedP_positive {t : ℝ} (ht : t ∈ Icc 0 seedT) : 0 < seedP t := by
  by_cases h : t ≤ seedCut
  · simpa only [seedP,h,ite_true] using seedPNew_positive ⟨ht.1,h⟩
  · simpa only [seedP,h,ite_false] using seedPCap_positive ⟨(lt_of_not_ge h).le,ht.2⟩
theorem seedDet_positive {t : ℝ} (ht : t ∈ Icc 0 seedT) : 0 < seedDet t := by
  by_cases h : t ≤ seedCut
  · have hp := seedDetNew_positive ⟨ht.1,h⟩
    simpa only [seedDet,seedP,seedNegQ,seedRAt,h,ite_true,seedDetNew,seedNegQNew] using hp
  · have hp := seedDetCap_positive ⟨(lt_of_not_ge h).le,ht.2⟩
    simpa only [seedDet,seedP,seedNegQ,seedRAt,h,ite_false,seedDetCap,seedNegQCap] using hp
theorem seedNegQ_positive {t : ℝ} (ht : 0 < t) (htT : t ≤ seedT) : 0 < seedNegQ t := by
  have hv := seedV_positive ⟨ht.le,htT⟩
  have hs := seedSlope_positive ⟨ht.le,htT⟩
  have hc := seedC_positive
  have hr := seedRAt_positive ⟨ht.le,htT⟩
  rw [seedNegQ_formula]
  positivity
end KLSBelow25.AffineSameTestCreationSeed238452
#print axioms KLSBelow25.AffineSameTestCreationSeed238452.seedP_formula
#print axioms KLSBelow25.AffineSameTestCreationSeed238452.seedP_positive
#print axioms KLSBelow25.AffineSameTestCreationSeed238452.seedDet_positive
#print axioms KLSBelow25.AffineSameTestCreationSeed238452.seedNegQ_positive

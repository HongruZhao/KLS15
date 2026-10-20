import KLSConstantImprovement.PiecewiseCreationSeed23847IntegerDet0
import KLSConstantImprovement.PiecewiseCreationSeed23847IntegerDet1
import KLSConstantImprovement.PiecewiseCreationSeed23847IntegerDet2
import KLSConstantImprovement.PiecewiseCreationSeed23847IntegerDet3
import KLSConstantImprovement.PiecewiseCreationSeed23847IntegerDet4
import KLSConstantImprovement.PiecewiseCreationSeed23847IntegerDet5
noncomputable section
open Set
namespace KLSBelow25.PiecewiseCreationSeed23847
open KLSBelow25.BernsteinInterval
open KLSConstantImprovement.IntegerListPolynomialCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem seedNegQ_formula (t : ℝ) : seedNegQ t = ((214623/2000)*seedC+64/(3*seedC))*t*seedV t+seedRAt t*t*(seedV t)^2*seedSlope t := rfl
theorem seedDet_positive {t : ℝ} (ht : t ∈ Icc 0 seedT) : 0 < seedDet t := by
  by_cases h0 : t ≤ seedCut0
  · have hp := seedDet0_positive ⟨ht.1, h0⟩
    simpa only [seedDet, seedNegQ, seedRAt, h0, ite_true, ite_false, seedDet0, seedNegQ0] using hp
  by_cases h1 : t ≤ seedCut1
  · have hp := seedDet1_positive ⟨(lt_of_not_ge h0).le, h1⟩
    simpa only [seedDet, seedNegQ, seedRAt, h0, h1, ite_true, ite_false, seedDet1, seedNegQ1] using hp
  by_cases h2 : t ≤ seedCut2
  · have hp := seedDet2_positive ⟨(lt_of_not_ge h1).le, h2⟩
    simpa only [seedDet, seedNegQ, seedRAt, h0, h1, h2, ite_true, ite_false, seedDet2, seedNegQ2] using hp
  by_cases h3 : t ≤ seedCut3
  · have hp := seedDet3_positive ⟨(lt_of_not_ge h2).le, h3⟩
    simpa only [seedDet, seedNegQ, seedRAt, h0, h1, h2, h3, ite_true, ite_false, seedDet3, seedNegQ3] using hp
  by_cases h4 : t ≤ seedCut4
  · have hp := seedDet4_positive ⟨(lt_of_not_ge h3).le, h4⟩
    simpa only [seedDet, seedNegQ, seedRAt, h0, h1, h2, h3, h4, ite_true, ite_false, seedDet4, seedNegQ4] using hp
  have hp := seedDet5_positive ⟨(lt_of_not_ge h4).le, ht.2⟩
  simpa only [seedDet, seedNegQ, seedRAt, h0, h1, h2, h3, h4, ite_true, ite_false, seedDet5, seedNegQ5] using hp
theorem seedNegQ_positive {t : ℝ} (ht : 0 < t) (htT : t ≤ seedT) : 0 < seedNegQ t := by
  have hv := seedV_positive ⟨ht.le, htT⟩
  have hs := seedSlope_positive ⟨ht.le, htT⟩
  have hc := seedC_positive
  have hr := seedRAt_positive t
  rw [seedNegQ_formula]
  positivity
end KLSBelow25.PiecewiseCreationSeed23847
#print axioms KLSBelow25.PiecewiseCreationSeed23847.seedDet_positive
#print axioms KLSBelow25.PiecewiseCreationSeed23847.seedNegQ_positive

import Mathlib

/- Original ODECO coefficient-metric correction and full main receipts.
The original Bessel/Gram, same-kernel Lambda cap, regression charge and
same-field Hilbert triangle are explicit analytic/finite inputs. -/

namespace KLSConstantImprovement.OriginalFullMetricMainPaymentScalar

theorem metric_correction_from_gram
    (F P2 N c : ℝ) (hN : 0 ≤ N)
    (hkernel : F ^ 2 ≤ 4 * N * P2) (hgram : P2 ≤ 24 * c) :
    F ^ 2 ≤ 96 * N * c := by
  have hscaled : 4 * N * P2 ≤ 4 * N * (24 * c) :=
    mul_le_mul_of_nonneg_left hgram (by positivity)
  nlinarith

theorem metric_correction_joint_budget
    (F N c delta y d : ℝ) (hN : 0 ≤ N)
    (hmetric : F ^ 2 ≤ 96 * N * c)
    (hbudget : c + 4 * delta + 4 * y ≤ (8 / 3 : ℝ) * d) :
    F ^ 2 + 384 * N * delta + 384 * N * y ≤ 256 * N * d := by
  have hscaled : 96 * N * (c + 4 * delta + 4 * y) ≤
      96 * N * ((8 / 3 : ℝ) * d) :=
    mul_le_mul_of_nonneg_left hbudget (by positivity)
  nlinarith

theorem full_main_critical_norm
    (mainRoot coreRoot offRoot correctionRoot r : ℝ)
    (htriangle : mainRoot ≤ coreRoot + offRoot + (3 / 2 : ℝ) * correctionRoot)
    (hoff : offRoot ≤ 32 * r) (hcorr : correctionRoot ≤ 4 * r) :
    mainRoot ≤ coreRoot + 38 * r := by
  linarith

#print axioms KLSConstantImprovement.OriginalFullMetricMainPaymentScalar.metric_correction_from_gram
#print axioms KLSConstantImprovement.OriginalFullMetricMainPaymentScalar.metric_correction_joint_budget
#print axioms KLSConstantImprovement.OriginalFullMetricMainPaymentScalar.full_main_critical_norm

end KLSConstantImprovement.OriginalFullMetricMainPaymentScalar

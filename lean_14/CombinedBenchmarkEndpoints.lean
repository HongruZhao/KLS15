import KLS14452512512Combined
import ProductOriginalClassFour
import ExponentialBenchmarkAudit

/-! Public entry point for the imported universal improvement and the actual
product-exponential endpoint on the same original KLS test class. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace KLS4Research
open KLS KLSImprovement.ActualProductCumulants

theorem universal_upper_bound :
    universalPoincareConstant ≤ (56455127 / 3906250 : ℝ≥0∞) :=
  KLSImprovement.Combined14452512512.universalPoincareUpperCombined

theorem exponential_product_upper_four {n : ℕ} {f : Space n → ℝ}
    (hf : LocallyLipschitzTests (centeredProductMeasure n) f) :
    variance (centeredProductMeasure n) f ≤
      (4 : ℝ≥0∞) * energy (centeredProductMeasure n) f :=
  KLSImprovement.ProductOriginalFour.product_poincare_four hf

theorem exponential_product_constant_le_four (n : ℕ) :
    poincareConstant (centeredProductMeasure n) ≤ 4 :=
  KLSImprovement.ProductOriginalFour.product_poincareConstant_le_four n

end KLS4Research
#print axioms KLS4Research.universal_upper_bound
#print axioms KLS4Research.exponential_product_upper_four
#print axioms KLS4Research.exponential_product_constant_le_four
#print axioms KLSImprovement.Combined14452512512.product_benchmark_covariance_charge
#print axioms KLSImprovement.ProductCubic.actual_product_appell_energy_three_le_six_integral
#print axioms KLSImprovement.CombinedExponentialAudit.scalar_quartic_cap_is_sharp

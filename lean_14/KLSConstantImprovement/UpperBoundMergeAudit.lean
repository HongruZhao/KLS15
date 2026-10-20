import KLSConstantImprovement.Cubic239BellmanEndpoint
import KLSConstantImprovement.LongPrefixCubicBellmanEndpoint
import KLSConstantImprovement.SixHeadUniversalEndpoint
import KLSConstantImprovement.LongPrefixUniversalEndpoint
import KLSConstantImprovement.ProjectionGeometryPayment
import CombinedBenchmarkEndpoints
import KLS4Research.ExponentialOriginalSharpness
import ActualPairTensorSlotBounds
import ActualFourthCumulantFlatBound
import KLS.RegularMomentMapQuadratic

/-! Current entry point for the merged, proved universal upper reductions.
The strongest unconditional bound combines the longer universal degree prefix
with the correlated-cubic Bellman endgame, and is less than 14.345312364
on the original locally Lipschitz L2 test class.
The longer-prefix and base Bellman branches are retained independently.
The exponential product benchmark and its universal lower bound remain four.
The newer Hessian/Schatten interpolation notes are not theorem premises here.
-/
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal
namespace KLSConstantImprovement.UpperBoundMergeAudit
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration

theorem certified_universal_interval :
    (4 : ℝ≥0∞) ≤ universalPoincareConstant ∧
      universalPoincareConstant ≤ (280181882107013433/19531250000000000 : ℝ≥0∞) :=
  ⟨KLS4Research.ExponentialOriginalSharpness.universal_poincareConstant_lower_four,
    LongPrefixCubicBellmanEndpoint.universal_poincare_upper⟩

theorem best_unconditional_original_class {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : LocallyLipschitzTests μ f) :
    variance μ f ≤ (280181882107013433/19531250000000000 : ℝ≥0∞)*energy μ f :=
  LongPrefixCubicBellmanEndpoint.original_poincare hn hμ hf

theorem best_bound_lt_saved : LongPrefixCubicBellmanEndpoint.bound < 14365931903/1000000000 :=
  LongPrefixCubicBellmanEndpoint.bound_lt_previous

theorem exponential_benchmark_original_class {n : ℕ} {f : Space n → ℝ}
    (hf : LocallyLipschitzTests (KLSImprovement.ActualProductCumulants.centeredProductMeasure n) f) :
    variance (KLSImprovement.ActualProductCumulants.centeredProductMeasure n) f ≤
      (4 : ℝ≥0∞)*energy (KLSImprovement.ActualProductCumulants.centeredProductMeasure n) f :=
  KLS4Research.exponential_product_upper_four hf

theorem third_cumulant_matrix_sq_le_eight_norm_sq {n : ℕ}
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) (u : Space n) :
    matrixFrobeniusSq (thirdCumulantMatrix μ u) ≤ 8*‖u‖^2 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  exact hμ.isotropic.thirdCumulant_frobeniusSq_le hμ.quadraticVarianceEight_unconditional u

end KLSConstantImprovement.UpperBoundMergeAudit

#check KLSConstantImprovement.Cubic239BellmanEndpoint.original_poincare
#check KLSConstantImprovement.Cubic239BellmanEndpoint.openai_poincare
#check KLSConstantImprovement.LongPrefixCubicBellmanEndpoint.original_poincare
#check KLSConstantImprovement.LongPrefixCubicBellmanEndpoint.openai_poincare
#check KLSConstantImprovement.SixHeadUniversalEndpoint.original_poincare
#check KLSConstantImprovement.LongPrefixUniversalEndpoint.original_poincare
#check KLSConstantImprovement.ProjectionGeometryPayment.actual_projection_observation_refined_shared_payment
#check KLS.DeterministicBridgeIntegration.actual_pair_kernel_square_le_eight
#check KLS.DeterministicBridgeIntegration.actual_pair_kernel_cross_le_four
#check KLS.DeterministicBridgeIntegration.actual_cubic_creation_square_le
#check KLS.DeterministicBridgeIntegration.actual_fourth_cumulant_flat_square_le
#check KLS.quadraticVarianceEight_of_regular_bounded_momentMap

#print axioms KLSConstantImprovement.UpperBoundMergeAudit.certified_universal_interval
#print axioms KLSConstantImprovement.UpperBoundMergeAudit.best_unconditional_original_class
#print axioms KLSConstantImprovement.UpperBoundMergeAudit.best_bound_lt_saved
#print axioms KLSConstantImprovement.UpperBoundMergeAudit.exponential_benchmark_original_class
#print axioms KLSConstantImprovement.UpperBoundMergeAudit.third_cumulant_matrix_sq_le_eight_norm_sq
#print axioms KLSConstantImprovement.Cubic239BellmanEndpoint.original_poincare_mem
#print axioms KLSConstantImprovement.Cubic239BellmanEndpoint.original_poincare
#print axioms KLSConstantImprovement.Cubic239BellmanEndpoint.universal_poincare_upper
#print axioms KLSConstantImprovement.Cubic239BellmanEndpoint.openai_poincare
#print axioms KLSConstantImprovement.LongPrefixCubicBellmanEndpoint.original_poincare_mem
#print axioms KLSConstantImprovement.LongPrefixCubicBellmanEndpoint.original_poincare
#print axioms KLSConstantImprovement.LongPrefixCubicBellmanEndpoint.universal_poincare_upper
#print axioms KLSConstantImprovement.LongPrefixCubicBellmanEndpoint.openai_poincare
#print axioms KLSConstantImprovement.LongPrefixCubicBellmanEndpoint.universal_poincare_rounded
#print axioms KLSConstantImprovement.SixHeadUniversalEndpoint.original_poincare
#print axioms KLSConstantImprovement.SixHeadUniversalEndpoint.universal_poincare_upper
#print axioms KLSConstantImprovement.LongPrefixUniversalEndpoint.original_poincare
#print axioms KLSConstantImprovement.LongPrefixUniversalEndpoint.universal_poincare_upper
#print axioms KLSConstantImprovement.ProjectionGeometryPayment.actual_projection_observation_refined_shared_payment
#print axioms KLS.DeterministicBridgeIntegration.actual_pair_kernel_square_le_eight
#print axioms KLS.DeterministicBridgeIntegration.actual_pair_kernel_cross_le_four
#print axioms KLS.DeterministicBridgeIntegration.actual_cubic_creation_square_le
#print axioms KLS.DeterministicBridgeIntegration.actual_fourth_cumulant_flat_square_le
#print axioms KLS.DeterministicBridgeNext.actualAppellEnergy_two_le_eight_integral
#print axioms KLS.quadraticVarianceEight_of_regular_bounded_momentMap
#print axioms KLS4Research.exponential_product_upper_four
#print axioms KLS4Research.exponential_product_constant_le_four
#print axioms KLS4Research.ExponentialOriginalSharpness.universal_poincareConstant_lower_four
#print axioms KLSImprovement.ProductCubic.actual_product_appell_energy_three_le_six_integral
#print axioms KLSImprovement.CombinedExponentialAudit.scalar_quartic_cap_is_sharp

import KLSConstantImprovement.ActualLargeDeficitAdditiveSector
import KLSConstantImprovement.OptimizedSeed23849BellmanEndpoint

/-! Transfer any proved Poincare constant to the literal additive-deficit
sector.  The final specialization uses the exact23849 endpoint.  The
complementary deficit range remains an explicit unresolved requirement. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal
namespace KLSConstantImprovement.PoincareDeficitSectorTransfer
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise
open ActualDeficitTensorBounds ActualCubicRepresenter ActualFixedTensorDeficit
open ActualCubicPoincareFourthSector ActualDeficitBesselBound
open ActualCubicRegressionSectorCriteria
set_option maxHeartbeats 2000000

theorem tensorPolynomial_variance_le_of_poincare_mem {n : ℕ}
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c, T a b c = T b a c) (hT23 : ∀ a b c, T a b c = T a c b)
    {c : ℝ≥0} (hc : c ∈ poincareConstants μ) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ ≤
      9 * (c : ℝ) * (fourthContraction μ T + 2 * tensorSquare T) := by
  have hbound := hc (tensorPolynomial μ T) (ActualCubicGradientEnergy.tensorPolynomial_original_test hμ T)
  rw [tensorPolynomial_extended_energy hμ T hT12 hT23] at hbound
  have hright : (c : ℝ≥0∞) *
      ENNReal.ofReal (9 * (fourthContraction μ T + 2 * tensorSquare T)) ≠ ⊤ :=
    ne_of_lt (ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top)
  have hr := ENNReal.toReal_mono hright hbound
  change ProbabilityTheory.variance (tensorPolynomial μ T) μ ≤ _ at hr
  have hE : 0 ≤ 9 * (fourthContraction μ T + 2 * tensorSquare T) := by
    rw [← tensorPolynomial_gradient_energy hμ T hT12 hT23]
    exact integral_nonneg fun _ => sq_nonneg _
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hE] at hr
  have hcast : (c : ℝ≥0∞).toReal = (c : ℝ) := rfl
  rw [hcast] at hr
  nlinarith

theorem poincare_deficit_scalar_gate {c N d F S V : ℝ}
    (hc : 0 ≤ c) (hd : d = 6 * N - F)
    (hlarge : (8 - 224 / (9 * c + 21)) * N ≤ d)
    (hS : -(F + 2 * N) ≤ S) (hV : V ≤ 9 * c * (F + 2 * N)) :
    0 ≤ 224 * N + 21 * S - V := by
  have hpositive : 0 < 9 * c + 21 := by positivity
  have hlarge' := mul_le_mul_of_nonneg_left hlarge hpositive.le
  have hpay : (9 * c + 21) * ((8 - 224 / (9 * c + 21)) * N) =
      (8 * (9 * c + 21) - 224) * N := by
    field_simp [hpositive.ne']
    <;> ring
  rw [hpay] at hlarge'
  have hQ : F + 2 * N = 8 * N - d := by linarith
  rw [hQ] at hS hV
  nlinarith

theorem original_additive_balance_of_poincare_and_large_deficit {n : ℕ}
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c, T a b c = T b a c) (hT23 : ∀ a b c, T a b c = T a c b)
    {c : ℝ≥0} (hc : c ∈ poincareConstants μ)
    (hlarge : (8 - 224 / (9 * (c : ℝ) + 21)) * tensorSquare T ≤ sliceDeficit μ T) :
    0 ≤ contractedDeficitHessian μ T + 21 * sliceDeficit μ T + 92 * tensorSquare T := by
  rw [additive_deficit_balance_eq hμ T hT12 hT23]
  exact poincare_deficit_scalar_gate c.property (by rfl) hlarge
    (signedTraceSquare_bounds_by_fourth_add_two hμ T).1
    (tensorPolynomial_variance_le_of_poincare_mem hμ T hT12 hT23 hc)

def threshold : ℝ := 953962184042043508549576 / 146589023005255438568697

theorem current_threshold_formula :
    8 - 224 / (9 * ((14009023389472826507633 / 976562500000000000000 : ℝ≥0) : ℝ) + 21) =
      threshold := by norm_num [threshold]

theorem current_threshold_positive : 0 < threshold := by norm_num [threshold]

theorem current_threshold_lt_previous : threshold < (4884344 / 750543 : ℝ) := by
  norm_num [threshold]

theorem current_original_large_deficit_additive_balance {n : ℕ}
    {μ : Measure (Space n)} (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ a b c, T a b c = T b a c)
    (hT23 : ∀ a b c, T a b c = T a c b)
    (hlarge : threshold * tensorSquare T ≤ sliceDeficit μ T) :
    0 ≤ contractedDeficitHessian μ T + 21 * sliceDeficit μ T + 92 * tensorSquare T := by
  apply original_additive_balance_of_poincare_and_large_deficit hμ T hT12 hT23
    (OptimizedSeed23849BellmanEndpoint.original_poincare_mem hn hμ)
  simpa only [current_threshold_formula] using hlarge

end KLSConstantImprovement.PoincareDeficitSectorTransfer

#print axioms KLSConstantImprovement.PoincareDeficitSectorTransfer.tensorPolynomial_variance_le_of_poincare_mem
#print axioms KLSConstantImprovement.PoincareDeficitSectorTransfer.poincare_deficit_scalar_gate
#print axioms KLSConstantImprovement.PoincareDeficitSectorTransfer.original_additive_balance_of_poincare_and_large_deficit
#print axioms KLSConstantImprovement.PoincareDeficitSectorTransfer.current_threshold_formula
#print axioms KLSConstantImprovement.PoincareDeficitSectorTransfer.current_threshold_lt_previous
#print axioms KLSConstantImprovement.PoincareDeficitSectorTransfer.current_original_large_deficit_additive_balance

import KLSConstantImprovement.CombinedObjectiveVarianceEquivalence
import KLSConstantImprovement.ActualRegularCubicVarianceReduction

/-! The exact remaining actual-law compact-test objective. Probability,
literal cubic C1/L2 membership, the paper-regular potential witness, and
target approximation are discharged. The all-tensor all-test numerical
objective bound remains OPEN. No source matrix field, optimizer, or
Poisson construction is assumed by this target-law reduction. -/
noncomputable section
open MeasureTheory ProbabilityTheory KLS
open scoped ContDiff
namespace KLSConstantImprovement.ActualRegularCubicCompactObjective
open KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise ActualDeficitTensorBounds ActualCubicRepresenter
open ActualCubicGradientEnergy ActualCombinedEnergyVarianceReduction
open CombinedObjectiveVarianceEquivalence ActualRegularCubicVarianceReduction

def RegularCubicCompactObjectiveBound (H : ℝ) : Prop :=
  ∀ {n : ℕ} {μ : Measure (Space n)}, admissibleMeasure μ → HasPaperRegularDensity μ →
    ∀ (V : Space n → ℝ), ContDiff ℝ 2 V → μ = potentialMeasure V →
    ∀ (T : Array3 (Fin n)) (hT12 : ∀ i j k, T i j k = T j i k)
      (hT23 : ∀ i j k, T i j k = T i k j),
      CombinedGradientBochnerBudget V (tensorPolynomial μ T) (H * tensorSquare T)

theorem literal_cubic_compact_objective_iff_variance {n : ℕ}
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {V : Space n → ℝ} (hV : ContDiff ℝ 2 V) (heq : μ = potentialMeasure V)
    (T : Array3 (Fin n)) {H : ℝ} :
    CombinedGradientBochnerBudget V (tensorPolynomial μ T) (H * tensorSquare T) ↔
      ProbabilityTheory.variance (tensorPolynomial μ T) μ ≤ H * tensorSquare T := by
  letI : IsProbabilityMeasure (potentialMeasure V) := by
    rw [← heq]
    exact hμ.isProb
  have hf2 : MemLp (tensorPolynomial μ T) 2 (potentialMeasure V) := by
    rw [← heq]
    exact tensorPolynomial_memLp hμ T
  have h := combined_budget_iff_variance_bound (K := H * tensorSquare T) hV
    ((tensorPolynomial_contDiff μ T).of_le (by simp)) hf2
  simpa only [← heq] using h

theorem regular_compact_objective_iff_literal_cap {H : ℝ} :
    RegularCubicCompactObjectiveBound H ↔ RegularLiteralCubicVarianceBound H := by
  constructor
  · intro hbudget n μ hμ hregular T hT12 hT23
    have hclass := hregular
    obtain ⟨V, κ, hV, hκ, hc, hupper, hgrowth, heq⟩ := hregular
    exact (literal_cubic_compact_objective_iff_variance hμ
      (hV.of_le (by simp)) heq T).mp
      (hbudget hμ hclass V (hV.of_le (by simp)) heq T hT12 hT23)
  · intro hcap n μ hμ hregular V hV heq T hT12 hT23
    exact (literal_cubic_compact_objective_iff_variance hμ hV heq T).mpr
      (hcap hμ hregular T hT12 hT23)

theorem universal_poincare_lt_fourteen_of_regular_compact_objective336
    (hbudget : RegularCubicCompactObjectiveBound 336) :
    universalPoincareConstant < 14 :=
  universal_poincare_lt_fourteen_of_regular_cubic336
    (regular_compact_objective_iff_literal_cap.mp hbudget)

end KLSConstantImprovement.ActualRegularCubicCompactObjective
#print axioms KLSConstantImprovement.ActualRegularCubicCompactObjective.literal_cubic_compact_objective_iff_variance
#print axioms KLSConstantImprovement.ActualRegularCubicCompactObjective.regular_compact_objective_iff_literal_cap
#print axioms KLSConstantImprovement.ActualRegularCubicCompactObjective.universal_poincare_lt_fourteen_of_regular_compact_objective336

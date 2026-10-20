import KLSConstantImprovement.ActualRegularCubicVarianceReduction
import KLS.StrongBoundedDensityApproximation

/-!
Literal cubic variance reduction to the bounded strongly convex target class.

The actual normalized weak moment source is available on precisely this class.
This module proves that no global smooth moment-map upgrade is needed for the
target approximation: a uniform literal cubic inequality on bounded strongly
convex targets suffices for every original admissible law. The numerical cubic
inequality on that class remains the only hypothesis; it is not asserted here.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Matrix Metric
open scoped Topology ENNReal ContDiff
namespace KLSConstantImprovement.ActualBoundedStrongCubicVarianceReduction
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise
open ActualDeficitTensorBounds ActualCubicRepresenter ActualCubicGradientEnergy
open ActualCubicRawMomentTransfer ActualCubicWeakTargetTransfer ActualTargetWeakApproximation
open ActualRegularCubicVarianceReduction
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def BoundedStrongLiteralCubicVarianceBound (H : ℝ) : Prop :=
  ∀ {n : ℕ} {μ : Measure (Space n)}, admissibleMeasure μ →
    HasSmoothBoundedStronglyConvexDensity μ →
    ∀ (T : Array3 (Fin n)) (hT12 : ∀ i j k, T i j k = T j i k)
      (hT23 : ∀ i j k, T i j k = T i k j),
      variance (tensorPolynomial μ T) μ ≤ H * tensorSquare T

/-- The actual vanishing quadratic damping and covariance whitening give
bounded strongly convex target laws. Weak probability convergence transfers
the literal cubic variance; it does not require convergence of source maps. -/
theorem literal_raw_cap_of_smoothBoundedDensity
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (hreg : HasSmoothBoundedConvexDensity μ)
    {H : ℝ} (hH : 0 ≤ H) (hstrong : BoundedStrongLiteralCubicVarianceBound H)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k, T i j k = T j i k)
    (hT23 : ∀ i j k, T i j k = T i k j) :
    variance (tensorPolynomial μ T) μ ≤ H * tensorSquare T := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  let ν : ℕ → ProbabilityMeasure (Space n) :=
    fun k => dampedWhitenedProbability hμ (cutoffScale k) (cutoffScale_pos k).le
  have hν (k : ℕ) : measureLogConcave (ν k : Measure (Space n)) := by
    change measureLogConcave (whitenedMeasure (quadraticDamping μ (cutoffScale k)))
    letI : IsProbabilityMeasure (quadraticDamping μ (cutoffScale k)) :=
      isProbabilityMeasure_quadraticDamping_nonneg μ (cutoffScale_pos k).le
    exact (hreg.quadraticDamping_logConcave (cutoffScale_pos k).le).whitenedMeasure
  have hcap : ∀ᶠ k in atTop,
      variance (fixedTensorCubic T) (ν k : Measure (Space n)) ≤ H * tensorSquare T := by
    filter_upwards [hμ.eventually_strongDensity_whitened_quadraticDamping hreg] with k hk
    have hh := hstrong hk.1 hk.2 T hT12 hT23
    letI : IsProbabilityMeasure (whitenedMeasure (quadraticDamping μ (cutoffScale k))) := hk.1.isProb
    change variance (fixedTensorCubic T)
      (whitenedMeasure (quadraticDamping μ (cutoffScale k))) ≤ H * tensorSquare T
    simpa only [tensorPolynomial_variance_fixed] using hh
  have hbound := memLp_and_variance_le_of_weak_target_limit
    (fixedTensorCubic_contDiff T).continuous
    (mul_nonneg hH (CubicVarianceFourthSector.tensorSquare_nonneg T))
    (damped_whitened_probability_tendsto hμ
      (fun k => (cutoffScale_pos k).le) cutoffScale_tendsto_zero)
    (fun k => fixedTensorCubic_memLp_logConcave (hν k) T) hcap
  rw [tensorPolynomial_variance_fixed]
  exact hbound.2

/-- The second actual cutoff and whitening reduce a global smooth convex
target law to the bounded class supporting the constructed weak source. -/
theorem literal_raw_cap_of_globalSmoothDensity
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {V : Space n → ℝ} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hc : ConvexOn ℝ univ V) (heq : μ = potentialMeasure V)
    {H : ℝ} (hH : 0 ≤ H) (hstrong : BoundedStrongLiteralCubicVarianceBound H)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k, T i j k = T j i k)
    (hT23 : ∀ i j k, T i j k = T i k j) :
    variance (tensorPolynomial μ T) μ ≤ H * tensorSquare T := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨R, hRpos, hR, hevent⟩ := hμ.exists_whitened_compact_cutoffs
  let ν : ℕ → ProbabilityMeasure (Space n) := fun k => cutoffWhitenedProbability hμ hR k
  have hν (k : ℕ) : measureLogConcave (ν k : Measure (Space n)) := by
    letI : IsProbabilityMeasure (ballCutoffMeasure μ R k) :=
      isProbabilityMeasure_ballCutoffMeasure hR k
    exact (hμ.logConcave.ballCutoff_logConcave R k).whitenedMeasure
  have hcap : ∀ᶠ k in atTop,
      variance (fixedTensorCubic T) (ν k : Measure (Space n)) ≤ H * tensorSquare T := by
    filter_upwards [hevent,
      hμ.eventually_smoothBoundedDensity_whitenedBallCutoff hV hc heq hRpos hR]
        with k hk hr
    have hh := literal_raw_cap_of_smoothBoundedDensity hk.1 hr hH hstrong T hT12 hT23
    letI : IsProbabilityMeasure (whitenedBallCutoffMeasure μ R k) := hk.1.isProb
    change variance (fixedTensorCubic T) (whitenedBallCutoffMeasure μ R k) ≤ H * tensorSquare T
    simpa only [tensorPolynomial_variance_fixed] using hh
  have hbound := memLp_and_variance_le_of_weak_target_limit
    (fixedTensorCubic_contDiff T).continuous
    (mul_nonneg hH (CubicVarianceFourthSector.tensorSquare_nonneg T))
    (cutoff_whitened_probability_tendsto hμ hR)
    (fun k => fixedTensorCubic_memLp_logConcave (hν k) T) hcap
  rw [tensorPolynomial_variance_fixed]
  exact hbound.2

/-- The retained paper-regular target class also reduces to the bounded
strong class by actual laws. No source or derivative regularity is supplied. -/
theorem regular_literal_bound_of_boundedStrong
    {H : ℝ} (hH : 0 ≤ H) (hstrong : BoundedStrongLiteralCubicVarianceBound H) :
    RegularLiteralCubicVarianceBound H := by
  intro n μ hμ hreg T hT12 hT23
  obtain ⟨V, κ, hV, hκ, hc, _, _, heq⟩ := hreg
  exact literal_raw_cap_of_globalSmoothDensity hμ hV
    (convexOn_of_strongConvexOn_nonneg hκ.le hc) heq hH hstrong T hT12 hT23

/-- Full original-law literal-cubic reduction. The only remaining premise
is the desired all-tensor inequality on the exact bounded-strong target class
where `ActualBoundedCanonicalSource.exists_sourceData` constructs the source. -/
theorem original_literal_raw_cap_of_boundedStrong_class
    {H : ℝ} (hH : 0 ≤ H) (hstrong : BoundedStrongLiteralCubicVarianceBound H) :
    LiteralCubicVarianceObservationTransfer.UniversalLiteralCubicVarianceBound H :=
  original_literal_raw_cap_of_regular_class hH
    (regular_literal_bound_of_boundedStrong hH hstrong)

theorem original_raw_observation_bound_of_boundedStrong_class
    {H : ℝ} (hH : 0 ≤ H) (hstrong : BoundedStrongLiteralCubicVarianceBound H) :
    RawCubicWeightedBudget.UniversalRawCubicBound H :=
  LiteralCubicVarianceObservationTransfer.rawCubicBound_of_tensor_variance hH
    (original_literal_raw_cap_of_boundedStrong_class hH hstrong)

end KLSConstantImprovement.ActualBoundedStrongCubicVarianceReduction

#print axioms KLSConstantImprovement.ActualBoundedStrongCubicVarianceReduction.literal_raw_cap_of_smoothBoundedDensity
#print axioms KLSConstantImprovement.ActualBoundedStrongCubicVarianceReduction.literal_raw_cap_of_globalSmoothDensity
#print axioms KLSConstantImprovement.ActualBoundedStrongCubicVarianceReduction.regular_literal_bound_of_boundedStrong
#print axioms KLSConstantImprovement.ActualBoundedStrongCubicVarianceReduction.original_literal_raw_cap_of_boundedStrong_class
#print axioms KLSConstantImprovement.ActualBoundedStrongCubicVarianceReduction.original_raw_observation_bound_of_boundedStrong_class

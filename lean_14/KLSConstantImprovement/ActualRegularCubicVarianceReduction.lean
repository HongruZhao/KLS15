import KLSConstantImprovement.ActualTargetWeakApproximation
import KLSConstantImprovement.ActualCubicWeakTargetTransfer
import KLSConstantImprovement.LiteralCubicVarianceObservationTransfer
import KLSConstantImprovement.RawCubic336ConditionalEndpoint
import KLSConstantImprovement.CubicVarianceFourthSector

/-! A literal cubic cap on the retained paper-regular target class suffices
for every original law. Actual cutoff, Gaussian, damping and whitening
approximation is discharged; no source or Poisson fields are passed.
The sole numerical premise is the all-tensor variance cap on actual
admissible HasPaperRegularDensity laws. That cap remains OPEN. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Matrix Metric
open scoped Topology ENNReal ContDiff
namespace KLSConstantImprovement.ActualRegularCubicVarianceReduction
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise
open ActualDeficitTensorBounds ActualCubicRepresenter ActualCubicGradientEnergy
open ActualCubicRawMomentTransfer ActualCubicWeakTargetTransfer ActualTargetWeakApproximation
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def RegularLiteralCubicVarianceBound (H : ℝ) : Prop :=
  ∀ {n : ℕ} {μ : Measure (Space n)}, admissibleMeasure μ → HasPaperRegularDensity μ →
    ∀ (T : Array3 (Fin n)) (hT12 : ∀ i j k, T i j k = T j i k)
      (hT23 : ∀ i j k, T i j k = T i k j),
      ProbabilityTheory.variance (tensorPolynomial μ T) μ ≤ H * tensorSquare T

theorem fixedTensorCubic_memLp_logConcave {ρ : Measure (Space n)} [IsProbabilityMeasure ρ]
    (hρ : measureLogConcave ρ) (T : Array3 (Fin n)) : MemLp (fixedTensorCubic T) 2 ρ := by
  unfold fixedTensorCubic
  rw [← tensorMvPolynomial_eval]
  exact polynomialEval_memLp_two hρ _

theorem literal_raw_cap_of_smooth_global
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {V : Space n → ℝ} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hc : ConvexOn ℝ univ V) (heq : μ = potentialMeasure V)
    (hupper : HasHessianUpperBound V) (hgrowth : HasPolynomialDerivativeGrowth V)
    {H : ℝ} (hH : 0 ≤ H) (hregular : RegularLiteralCubicVarianceBound H)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k, T i j k = T j i k)
    (hT23 : ∀ i j k, T i j k = T i k j) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ ≤ H * tensorSquare T := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  let ν : ℕ → ProbabilityMeasure (Space n) :=
    fun k => dampedWhitenedProbability hμ (cutoffScale k) (cutoffScale_pos k).le
  have hν (k : ℕ) : measureLogConcave (ν k : Measure (Space n)) := by
    change measureLogConcave (whitenedMeasure (quadraticDamping μ (cutoffScale k)))
    letI : IsProbabilityMeasure (quadraticDamping μ (cutoffScale k)) :=
      isProbabilityMeasure_quadraticDamping_nonneg μ (cutoffScale_pos k).le
    exact (measureLogConcave_quadraticDamping_of_potential hV hc heq
      (cutoffScale_pos k).le).whitenedMeasure
  have hcap : ∀ᶠ k in atTop,
      ProbabilityTheory.variance (fixedTensorCubic T) (ν k : Measure (Space n)) ≤
        H * tensorSquare T := by
    filter_upwards [eventually_admissible_paperRegularDensity_whitened_damping hμ
      (fun k => (cutoffScale_pos k).le) cutoffScale_tendsto_zero hV hc heq
      hupper hgrowth cutoffScale_pos] with k hk
    have hh := hregular hk.1 hk.2 T hT12 hT23
    letI : IsProbabilityMeasure (whitenedMeasure (quadraticDamping μ (cutoffScale k))) := hk.1.isProb
    change ProbabilityTheory.variance (fixedTensorCubic T)
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

theorem literal_raw_cap_of_compact_law
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) (hs : IsCompact μ.support)
    {H : ℝ} (hH : 0 ≤ H) (hregular : RegularLiteralCubicVarianceBound H)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k, T i j k = T j i k)
    (hT23 : ∀ i j k, T i j k = T i k j) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ ≤ H * tensorSquare T := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  let ν : ℕ → ProbabilityMeasure (Space n) := fun k => gaussianProbability μ (cutoffScale k)
  have hν (k : ℕ) : admissibleMeasure (ν k : Measure (Space n)) :=
    hμ.isotropicGaussianSmoothing (cutoffScale_pos k).ne'
  have hcap : ∀ᶠ k in atTop,
      ProbabilityTheory.variance (fixedTensorCubic T) (ν k : Measure (Space n)) ≤
        H * tensorSquare T := by
    apply Eventually.of_forall
    intro k
    have hr := (cutoffScale_pos k).ne'
    have hGauss := isotropicGaussianPotential_contDiff hs hr
    have hupper : HasHessianUpperBound (isotropicGaussianPotential μ (cutoffScale k)) :=
      (hasHessianUpperBound_gaussianSmoothedPotential hs hr).scalarTransformedPotential
        ((gaussianSmoothedPotential_contDiff hs hr).of_le (by simp)) _
    have hgrowth : HasPolynomialDerivativeGrowth (isotropicGaussianPotential μ (cutoffScale k)) :=
      (hasPolynomialDerivativeGrowth_gaussianSmoothedPotential hs hr).scalarTransformedPotential
        (gaussianSmoothedPotential_contDiff hs hr) _
    have hh := literal_raw_cap_of_smooth_global (hν k) hGauss
      (hμ.isotropicGaussianPotential_convex hs hr)
      (hμ.isotropicGaussianSmoothing_eq_exp_potential hs hr)
      hupper hgrowth hH hregular T hT12 hT23
    simpa only [tensorPolynomial_variance_fixed] using hh
  have hbound := memLp_and_variance_le_of_weak_target_limit
    (fixedTensorCubic_contDiff T).continuous
    (mul_nonneg hH (CubicVarianceFourthSector.tensorSquare_nonneg T))
    (gaussian_probability_tendsto μ)
    (fun k => fixedTensorCubic_memLp (hν k) T) hcap
  rw [tensorPolynomial_variance_fixed]
  exact hbound.2

theorem original_literal_raw_cap_of_regular_class
    {H : ℝ} (hH : 0 ≤ H) (hregular : RegularLiteralCubicVarianceBound H) :
    LiteralCubicVarianceObservationTransfer.UniversalLiteralCubicVarianceBound H := by
  intro n μ hμ T hT12 hT23
  letI : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨R, _, hR, hevent⟩ := hμ.exists_whitened_compact_cutoffs
  let ν : ℕ → ProbabilityMeasure (Space n) := fun k => cutoffWhitenedProbability hμ hR k
  have hν (k : ℕ) : measureLogConcave (ν k : Measure (Space n)) := by
    letI : IsProbabilityMeasure (ballCutoffMeasure μ R k) :=
      isProbabilityMeasure_ballCutoffMeasure hR k
    exact (hμ.logConcave.ballCutoff_logConcave R k).whitenedMeasure
  have hcap : ∀ᶠ k in atTop,
      ProbabilityTheory.variance (fixedTensorCubic T) (ν k : Measure (Space n)) ≤
        H * tensorSquare T := by
    filter_upwards [hevent] with k hk
    have hh := literal_raw_cap_of_compact_law hk.1 hk.2 hH hregular T hT12 hT23
    letI : IsProbabilityMeasure (whitenedBallCutoffMeasure μ R k) := hk.1.isProb
    change ProbabilityTheory.variance (fixedTensorCubic T)
      (whitenedBallCutoffMeasure μ R k) ≤ H * tensorSquare T
    simpa only [tensorPolynomial_variance_fixed] using hh
  have hbound := memLp_and_variance_le_of_weak_target_limit
    (fixedTensorCubic_contDiff T).continuous
    (mul_nonneg hH (CubicVarianceFourthSector.tensorSquare_nonneg T))
    (cutoff_whitened_probability_tendsto hμ hR)
    (fun k => fixedTensorCubic_memLp_logConcave (hν k) T) hcap
  rw [tensorPolynomial_variance_fixed]
  exact hbound.2

theorem original_raw_observation_bound_of_regular_class
    {H : ℝ} (hH : 0 ≤ H) (hregular : RegularLiteralCubicVarianceBound H) :
    RawCubicWeightedBudget.UniversalRawCubicBound H :=
  LiteralCubicVarianceObservationTransfer.rawCubicBound_of_tensor_variance hH
    (original_literal_raw_cap_of_regular_class hH hregular)

theorem universal_poincare_lt_fourteen_of_regular_cubic336
    (hregular : RegularLiteralCubicVarianceBound 336) :
    universalPoincareConstant < 14 :=
  RawCubic336ConditionalEndpoint.universal_poincare_lt_fourteen
    (original_raw_observation_bound_of_regular_class (by norm_num) hregular)

end KLSConstantImprovement.ActualRegularCubicVarianceReduction
#print axioms KLSConstantImprovement.ActualRegularCubicVarianceReduction.fixedTensorCubic_memLp_logConcave
#print axioms KLSConstantImprovement.ActualRegularCubicVarianceReduction.literal_raw_cap_of_smooth_global
#print axioms KLSConstantImprovement.ActualRegularCubicVarianceReduction.literal_raw_cap_of_compact_law
#print axioms KLSConstantImprovement.ActualRegularCubicVarianceReduction.original_literal_raw_cap_of_regular_class
#print axioms KLSConstantImprovement.ActualRegularCubicVarianceReduction.original_raw_observation_bound_of_regular_class
#print axioms KLSConstantImprovement.ActualRegularCubicVarianceReduction.universal_poincare_lt_fourteen_of_regular_cubic336

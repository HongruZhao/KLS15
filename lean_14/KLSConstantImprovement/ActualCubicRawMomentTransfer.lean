import KLSConstantImprovement.ActualCubicGradientEnergy

/-! Literal original-law cubic variances pass through target polynomial
moments. The centering depending on the law is only a constant shift of
a fixed cubic. Actual admissibility and convergence of the fixed cubic's
first and second moments remain explicit; no source, derivative, kernel
or Poisson field is passed by this module. No numerical cap is proved. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ContDiff Topology
namespace KLSConstantImprovement.ActualCubicRawMomentTransfer
open KLS KLS.DeterministicBridgeIntegration KLSBelow25.CubicSymmetricNoise
open ActualDeficitTensorBounds ActualCubicRepresenter ActualCubicGradientEnergy
variable {n : ℕ}

def fixedTensorCubic (T : Array3 (Fin n)) : Space n → ℝ :=
  tensorPolynomial (0 : Measure (Space n)) T

def tensorCenterShift (μ : Measure (Space n)) (T : Array3 (Fin n)) : ℝ :=
  ∑ a, ∑ b, ∑ c, T a b c *
    (actualThirdCubicArray μ a b c - actualThirdCubicArray (0 : Measure (Space n)) a b c)

theorem tensorPolynomial_fixed_shift (μ : Measure (Space n)) (T : Array3 (Fin n)) :
    tensorPolynomial μ T = fun x => fixedTensorCubic T x - tensorCenterShift μ T := by
  funext x
  have hc (a b c : Fin n) : coordinateCubic μ a b c x =
      coordinateCubic (0 : Measure (Space n)) a b c x -
        (actualThirdCubicArray μ a b c - actualThirdCubicArray (0 : Measure (Space n)) a b c) := by
    unfold coordinateCubic
    ring
  simp only [tensorPolynomial, fixedTensorCubic, tensorCenterShift]
  simp only [hc, mul_sub, Finset.sum_sub_distrib]

theorem fixedTensorCubic_contDiff (T : Array3 (Fin n)) :
    ContDiff ℝ (⊤ : ℕ∞) (fixedTensorCubic T) :=
  tensorPolynomial_contDiff (0 : Measure (Space n)) T

theorem fixedTensorCubic_memLp {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) : MemLp (fixedTensorCubic T) 2 μ := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have he : fixedTensorCubic T =
      fun x => tensorPolynomial μ T x + tensorCenterShift μ T := by
    funext x
    have h := congrFun (tensorPolynomial_fixed_shift μ T) x
    change tensorPolynomial μ T x = fixedTensorCubic T x - tensorCenterShift μ T at h
    linarith
  rw [he]
  exact (tensorPolynomial_memLp hμ T).add (memLp_const (tensorCenterShift μ T))

theorem tensorPolynomial_variance_fixed (μ ρ : Measure (Space n))
    [IsProbabilityMeasure ρ] (T : Array3 (Fin n)) :
    variance (tensorPolynomial μ T) ρ = variance (fixedTensorCubic T) ρ := by
  rw [tensorPolynomial_fixed_shift]
  exact variance_sub_const (fixedTensorCubic_contDiff T).continuous.aestronglyMeasurable _

theorem actual_cubic_variance_tendsto_of_moments
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {ν : ℕ → Measure (Space n)} (hν : ∀ k, admissibleMeasure (ν k))
    (T : Array3 (Fin n))
    (hmean : Tendsto (fun k => ∫ x, fixedTensorCubic T x ∂ν k) atTop
      (𝓝 (∫ x, fixedTensorCubic T x ∂μ)))
    (hsquare : Tendsto (fun k => ∫ x, (fixedTensorCubic T x)^2 ∂ν k) atTop
      (𝓝 (∫ x, (fixedTensorCubic T x)^2 ∂μ))) :
    Tendsto (fun k => variance (tensorPolynomial (ν k) T) (ν k)) atTop
      (𝓝 (variance (tensorPolynomial μ T) μ)) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  letI : ∀ k, IsProbabilityMeasure (ν k) := fun k => (hν k).isProb
  have hform (ρ : Measure (Space n)) (hρ : admissibleMeasure ρ) :
      variance (tensorPolynomial ρ T) ρ =
        (∫ x, (fixedTensorCubic T x)^2 ∂ρ) - (∫ x, fixedTensorCubic T x ∂ρ)^2 := by
    letI : IsProbabilityMeasure ρ := hρ.isProb
    rw [tensorPolynomial_variance_fixed]
    simpa only [Pi.pow_apply] using variance_eq_sub (fixedTensorCubic_memLp hρ T)
  have he : (fun k => variance (tensorPolynomial (ν k) T) (ν k)) =
      fun k => (∫ x, (fixedTensorCubic T x)^2 ∂ν k) - (∫ x, fixedTensorCubic T x ∂ν k)^2 := by
    funext k
    exact hform (ν k) (hν k)
  rw [he, hform μ hμ]
  simpa only [Pi.pow_apply, Pi.sub_apply] using hsquare.sub (hmean.pow 2)

theorem actual_cubic_raw_cap_of_target_moments
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {ν : ℕ → Measure (Space n)} (hν : ∀ k, admissibleMeasure (ν k))
    (T : Array3 (Fin n)) {C : ℝ}
    (hmean : Tendsto (fun k => ∫ x, fixedTensorCubic T x ∂ν k) atTop
      (𝓝 (∫ x, fixedTensorCubic T x ∂μ)))
    (hsquare : Tendsto (fun k => ∫ x, (fixedTensorCubic T x)^2 ∂ν k) atTop
      (𝓝 (∫ x, (fixedTensorCubic T x)^2 ∂μ)))
    (hcap : ∀ᶠ k in atTop, variance (tensorPolynomial (ν k) T) (ν k) ≤ C * tensorSquare T) :
    variance (tensorPolynomial μ T) μ ≤ C * tensorSquare T := by
  exact le_of_tendsto_of_tendsto
    (actual_cubic_variance_tendsto_of_moments hμ hν T hmean hsquare) tendsto_const_nhds hcap

end KLSConstantImprovement.ActualCubicRawMomentTransfer
#print axioms KLSConstantImprovement.ActualCubicRawMomentTransfer.tensorPolynomial_fixed_shift
#print axioms KLSConstantImprovement.ActualCubicRawMomentTransfer.fixedTensorCubic_contDiff
#print axioms KLSConstantImprovement.ActualCubicRawMomentTransfer.fixedTensorCubic_memLp
#print axioms KLSConstantImprovement.ActualCubicRawMomentTransfer.tensorPolynomial_variance_fixed
#print axioms KLSConstantImprovement.ActualCubicRawMomentTransfer.actual_cubic_variance_tendsto_of_moments
#print axioms KLSConstantImprovement.ActualCubicRawMomentTransfer.actual_cubic_raw_cap_of_target_moments

import KLSConstantImprovement.ActualDualCapCoercivity405
import KLSConstantImprovement.ActualSuperlinearGradientProper405
import KLSConstantImprovement.ActualTargetWeakApproximation
import KLS.MomentGradientRange

/-! The dual-cap barrier specialized to the actual isotropic bounded target
cutoffs. Full-support ball masses are proved from the genuine positive
potential density, and convergence is the actual cutoff/whitening theorem.
The displayed dual-energy bound must still be supplied by the actual
centered source construction. No inverse or Bochner assertion occurs. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric InnerProductSpace
open scoped Topology BigOperators ENNReal NNReal
namespace KLSConstantImprovement.ActualWhitenedCutoffConfinement405
open KLS ActualDualCapCoercivity405 ActualSuperlinearGradientProper405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem potential_density_ball_positive {μ : Measure (Space n)} {V : Space n → ℝ}
    (hV : Continuous V) (heq : μ = potentialMeasure V) (p : Space n) :
    0 < μ (ball p 1) := by
  apply pos_iff_ne_zero.mpr
  intro hz
  rw [heq] at hz
  have hv := volume_absolutelyContinuous_potentialMeasure_of_measurable hV.measurable hz
  exact (measure_ball_pos volume p (by norm_num : (0 : ℝ) < 1)).ne' hv

theorem actual_whitened_cutoff_uniform_cones (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {V : Space n → ℝ} (hV : Continuous V) (heq : μ = potentialMeasure V)
    {R : ℝ} (hR : μ (closedBall (0 : Space n) R) ≠ 0)
    {f : ℕ → Space n → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hE : ∀ k, momentDualEnergy (whitenedBallCutoffMeasure μ R k) (f k) ≤ ENNReal.ofReal K)
    {a : ℝ} (ha : 0 ≤ a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop, ∀ x, a * ‖x‖ - B ≤ f k x := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  letI : ∀ k, IsProbabilityMeasure (ballCutoffMeasure μ R k) := fun k =>
    isProbabilityMeasure_ballCutoffMeasure hR k
  letI : ∀ k, IsProbabilityMeasure (whitenedBallCutoffMeasure μ R k) := fun k =>
    inferInstanceAs (IsProbabilityMeasure (whitenedMeasure (ballCutoffMeasure μ R k)))
  exact uniform_cones_of_fullsupport_target_limit hn hK hE
    (potential_density_ball_positive hV heq)
    (fun _ hf hc => hμ.tendsto_integral_whitenedBallCutoffMeasure_compact hR hf hc) ha

theorem actual_whitened_cutoff_limit_gradient_proper (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {V : Space n → ℝ} (hV : Continuous V) (heq : μ = potentialMeasure V)
    {R : ℝ} (hR : μ (closedBall (0 : Space n) R) ≠ 0)
    {f : ℕ → Space n → ℝ} {φ : Space n → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hE : ∀ k, momentDualEnergy (whitenedBallCutoffMeasure μ R k) (f k) ≤ ENNReal.ofReal K)
    (hlim : ∀ x, Tendsto (fun k => f k x) atTop (𝓝 (φ x)))
    (hφ : ContDiff ℝ 1 φ) (hc : ConvexOn ℝ univ φ)
    {E : Set (Space n)} (hEcomp : IsCompact E) :
    IsCompact ((gradient φ) ⁻¹' E) := by
  apply gradient_preimage_compact hφ hc _ hEcomp
  exact cones_of_eventual_cones
    (fun a ha => actual_whitened_cutoff_uniform_cones hn hμ hV heq hR hK hE ha) hlim

end KLSConstantImprovement.ActualWhitenedCutoffConfinement405
#print axioms KLSConstantImprovement.ActualWhitenedCutoffConfinement405.potential_density_ball_positive
#print axioms KLSConstantImprovement.ActualWhitenedCutoffConfinement405.actual_whitened_cutoff_uniform_cones
#print axioms KLSConstantImprovement.ActualWhitenedCutoffConfinement405.actual_whitened_cutoff_limit_gradient_proper

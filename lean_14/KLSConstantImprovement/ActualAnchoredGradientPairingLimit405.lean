import KLSConstantImprovement.ActualC11SourceCompactness405
import KLS.WeakHessianTensorSymmetry

/-! Genuine compact-test convergence of the actual first derivatives.  The
common anchored gradient Lipschitz bound pays the integrable dominator; it
is not a supplied derivative pairing or weak-PDE certificate. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ContDiff
namespace KLSConstantImprovement.ActualAnchoredGradientPairingLimit405
open KLS ActualAnchoredLipschitzCompactness405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem actual_gradient_compact_pairing_tendsto
    {f : ℕ → Space n → ℝ} {φ : Space n → ℝ}
    (hf : ∀ k, ContDiff ℝ 1 (f k)) {L : ℝ≥0}
    (hL : ∀ k, LipschitzWith L (gradient (f k)))
    (h0 : ∀ k, gradient (f k) 0 = 0)
    (hlim : ∀ x, Tendsto (fun k => gradient (f k) x) atTop (𝓝 (gradient φ x)))
    {θ : Space n → ℝ} (hθ : Continuous θ) (hcθ : HasCompactSupport θ) (i : Fin n) :
    Tendsto (fun k => ∫ x, coordinateDerivative (f k) i x*θ x) atTop
      (𝓝 (∫ x, coordinateDerivative φ i x*θ x)) := by
  have hdom : Integrable (fun x : Space n => ((L : ℝ)*‖x‖)*‖θ x‖) volume :=
    ((continuous_const.mul continuous_norm).mul hθ.norm).integrable_of_hasCompactSupport
      hcθ.norm.mul_left
  apply tendsto_integral_of_dominated_convergence (fun x : Space n => ((L : ℝ)*‖x‖)*‖θ x‖)
  · intro k
    simp only [coordinateDerivative_eq_gradient]
    exact (((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp
      (continuous_gradient_of_contDiff (hf k))).mul hθ).aestronglyMeasurable
  · exact hdom
  · intro k
    exact Eventually.of_forall fun x => by
      rw [norm_mul, coordinateDerivative_eq_gradient]
      have hb : ‖gradient (f k) x‖ ≤ (L : ℝ)*‖x‖ :=
        anchored_lipschitz_bound (hL k) (h0 k) x
      exact mul_le_mul_of_nonneg_right
        ((PiLp.norm_apply_le (gradient (f k) x) i).trans hb) (norm_nonneg _)
  · exact Eventually.of_forall fun x => by
      simp only [coordinateDerivative_eq_gradient]
      exact (((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.continuousAt.tendsto.comp (hlim x)).mul_const (θ x))

end KLSConstantImprovement.ActualAnchoredGradientPairingLimit405
#print axioms KLSConstantImprovement.ActualAnchoredGradientPairingLimit405.actual_gradient_compact_pairing_tendsto

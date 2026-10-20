import KLSConstantImprovement.ActualAnchoredGradientPairingLimit405
import KLSConstantImprovement.ActualLocalCompactWeakTests405
import KLS.WeakDerivativeMollification

/-! The strong limits of the genuine source-Hessian cutoff fields are
the actual Hessian of the limiting source.  Identification uses the weak
derivative of the actual gradient and compact-test convergence; no Hessian
limit or derivative identity is supplied as a certificate. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ContDiff ENNReal
namespace KLSConstantImprovement.ActualSourceHessianLimitIdentification405
open KLS ActualBoundedCanonicalSource ActualBoundedRawTestAlgebra405
open ActualLocalBoundedWeakAlgebra405 ActualLocalCompactWeakTests405
open ActualAnchoredGradientPairingLimit405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {ρ : ℕ → Measure (Space n)} {μ : Measure (Space n)}

theorem actual_hessian_compact_multiplier_memLp (e : SourceData μ)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hcχ : HasCompactSupport χ)
    (a b : Fin n) :
    MemLp (fun x => χ x*coordinateHessian e.potential x a b) 2
      (volume : Measure (Space n)) := by
  let q := cutoffLocalRawTest hχ
    (LocalRawTest.ofBoundedRawTest (BoundedRawTest.hessian e a b))
  exact memLp_compact_of_localL2 q.value_local hcχ.mul_right

theorem actual_hessian_cutoff_limit_identified
    (d : ∀ k, SourceData (ρ k)) (e : SourceData μ) {L : ℝ≥0}
    (hL : ∀ k, LipschitzWith L (gradient (d k).potential))
    (h0 : ∀ k, gradient (d k).potential 0 = 0)
    (hlim : ∀ x, Tendsto (fun k => gradient (d k).potential x) atTop
      (𝓝 (gradient e.potential x)))
    {χ : Space n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (a b : Fin n) (g : Lp ℝ 2 (volume : Measure (Space n)))
    (hconv : Tendsto (fun k => eLpNorm
      (fun x => χ x*coordinateHessian (d k).potential x a b-g x) 2 volume)
      atTop (𝓝 0)) :
    (g : Space n → ℝ) =ᵐ[volume] (fun x => χ x*coordinateHessian e.potential x a b) := by
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by simp)
  have hf (k : ℕ) := actual_hessian_compact_multiplier_memLp (d k) hχ1 hcχ a b
  have he := actual_hessian_compact_multiplier_memLp e hχ1 hcχ a b
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp g).locallyIntegrable (by norm_num)) (he.locallyIntegrable (by norm_num))
  intro ψ hψ hcψ
  have hψ2 : MemLp ψ 2 (volume : Measure (Space n)) :=
    hψ.continuous.memLp_of_hasCompactSupport hcψ
  have hχψ : ContDiff ℝ ∞ (fun x => χ x*ψ x) := hχ.mul hψ
  have hcχψ : HasCompactSupport (fun x => χ x*ψ x) := hcχ.mul_right
  have hD : Continuous (coordinateDerivative (fun x => χ x*ψ x) a) :=
    (contDiff_coordinateDerivative hχψ (m := 0) (by simp) a).continuous
  have hcD : HasCompactSupport (coordinateDerivative (fun x => χ x*ψ x) a) :=
    hasCompactSupport_coordinateDerivative hcχψ a
  have htest (k : ℕ) :
      (∫ x, ψ x*(χ x*coordinateHessian (d k).potential x a b)) =
        -(∫ x, coordinateDerivative (d k).potential b x*
          coordinateDerivative (fun y => χ y*ψ y) a x) := by
    have hw := actual_hessian_hasLocalWeakCoordinateDerivative
      (d k).gradient_lipschitz.locallyLipschitz a b
      (fun x => χ x*ψ x) (hχψ.of_le (by simp)) hcχψ
    have hp : (∫ x, coordinateHessian (d k).potential x a b*(χ x*ψ x)) =
        ∫ x, ψ x*(χ x*coordinateHessian (d k).potential x a b) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    rw [hp] at hw
    linarith
  have htarget :
      (∫ x, ψ x*(χ x*coordinateHessian e.potential x a b)) =
        -(∫ x, coordinateDerivative e.potential b x*
          coordinateDerivative (fun y => χ y*ψ y) a x) := by
    have hw := actual_hessian_hasLocalWeakCoordinateDerivative
      e.gradient_lipschitz.locallyLipschitz a b
      (fun x => χ x*ψ x) (hχψ.of_le (by simp)) hcχψ
    have hp : (∫ x, coordinateHessian e.potential x a b*(χ x*ψ x)) =
        ∫ x, ψ x*(χ x*coordinateHessian e.potential x a b) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    rw [hp] at hw
    linarith
  have hl := tendsto_integral_mul_of_eLpNorm_sub_tendsto_zero
    hf (Lp.memLp g) hψ2 hconv
  have hr := (actual_gradient_compact_pairing_tendsto
    (fun k => (d k).source_C1) hL h0 hlim hD hcD b).neg
  have hr' : Tendsto
      (fun k => ∫ x, ψ x*(χ x*coordinateHessian (d k).potential x a b)) atTop
      (𝓝 (-(∫ x, coordinateDerivative e.potential b x*
        coordinateDerivative (fun y => χ y*ψ y) a x))) := by
    convert hr using 1
    funext k
    exact htest k
  have hid := tendsto_nhds_unique hl hr'
  simpa only [smul_eq_mul] using hid.trans htarget.symm

end KLSConstantImprovement.ActualSourceHessianLimitIdentification405
#print axioms KLSConstantImprovement.ActualSourceHessianLimitIdentification405.actual_hessian_compact_multiplier_memLp
#print axioms KLSConstantImprovement.ActualSourceHessianLimitIdentification405.actual_hessian_cutoff_limit_identified

import ActualLawTiltSmooth
import KLS.LinearCumulantTaylor
import Mathlib

/-! Literal coefficient-cumulant identity (3.19) for arbitrary log-concave
probability laws. Only a local exponential domain is used. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n : ℕ}
set_option maxHeartbeats 1000000

 theorem hasFDerivAt_logLaplace_of_local
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] {r : ℝ}
    (h1 : LocalNormExponentialDomain μ (fun _ => 1) r) {z : Space n} (hz : ‖z‖ < r) :
    HasFDerivAt (tiltLogLaplace μ)
      ((tiltPartition μ (fun x => inner ℝ z x))⁻¹ •
        (∫ x, Real.exp (inner ℝ z x) • innerSL ℝ x ∂μ)) z := by
  have hd : HasFDerivAt (fun z => tiltPartition μ (fun x => inner ℝ z x))
      (∫ x, Real.exp (inner ℝ z x) • innerSL ℝ x ∂μ) z := by
    have he : (fun w => tiltPartition μ (fun x => inner ℝ w x)) =
        tiltNumerator μ (fun _ => 0) (fun _ => 1) := by
      funext w
      simp only [tiltPartition,tiltNumerator,zero_add,one_mul]
    rw [he]
    simpa only [one_mul] using hasFDerivAt_tiltNumerator_of_localNormExponentialDomain h1 hz
  have hi : Integrable (fun x => Real.exp (inner ℝ z x)) μ := by
    simpa only [one_mul] using h1.integrable_tilt hz.le
  exact hd.log (integral_exp_pos hi).ne'

 theorem fderiv_logLaplace_direction_eq_average_of_local
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] {r : ℝ}
    (h1 : LocalNormExponentialDomain μ (fun _ => 1) r) {z : Space n} (hz : ‖z‖ < r)
    (u : Space n) :
    fderiv ℝ (tiltLogLaplace μ) z u = ∫ x, inner ℝ x u ∂exponentialTilt μ z := by
  have hi : Integrable (fun x => Real.exp (inner ℝ z x) • innerSL ℝ x) μ := by
    simpa only [one_mul] using h1.integrable_tilt_derivative hz.le
  rw [(hasFDerivAt_logLaplace_of_local h1 hz).fderiv]
  simp only [_root_.smul_apply,smul_eq_mul]
  rw [ContinuousLinearMap.integral_apply hi]
  change _ = tiltAverage μ (fun x => inner ℝ z x) (fun x => inner ℝ x u)
  rw [tiltAverage_eq_ratio]
  have he (x : Space n) : (Real.exp (inner ℝ z x) • innerSL ℝ x) u =
      inner ℝ x u*Real.exp (inner ℝ z x) := by
    simp only [_root_.smul_apply,smul_eq_mul,innerSL_apply_apply]
    ring
  simp_rw [he]
  ring

/-- Exact arbitrary-law (3.19), with the paper's unnormalized coefficient.
No next-rank cumulant norm estimate is assumed. -/
 theorem actualAppellCoefficient_inner_eq_cumulant
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) (u : Space n) (d : ℕ) (a : Fin d → Fin n) :
    actualAppellCoefficient μ (fun x => inner ℝ x u) d a =
      cumulantTensor μ (d+1)
        (Fin.snoc (fun j => EuclideanSpace.basisFun (Fin n) ℝ (a j)) u) := by
  obtain ⟨r,hr,hD⟩ := hLC.exists_localNormExponentialDomain_one
  have he : (fun z => ∫ x, inner ℝ x u ∂exponentialTilt μ z) =ᶠ[𝓝 (0 : Space n)]
      (fun z => fderiv ℝ (tiltLogLaplace μ) z u) := by
    filter_upwards [ball_mem_nhds (0 : Space n) hr] with z hz
    exact (fderiv_logLaplace_direction_eq_average_of_local hD
      (by simpa only [mem_ball,dist_zero_right] using hz) u).symm
  unfold actualAppellCoefficient
  rw [(he.iteratedFDeriv ℝ d).eq_of_nhds]
  have hh := iteratedFDeriv_directional_comp (ContinuousLinearMap.id ℝ (Space n)) 0 u
    ((hLC.contDiffAt_logLaplace).of_le (by simp) : ContDiffAt ℝ (d+1) (tiltLogLaplace μ) 0)
    (fun j => EuclideanSpace.basisFun (Fin n) ℝ (a j))
  simpa only [ContinuousLinearMap.id_apply,EuclideanSpace.basisFun_apply,cumulantTensor] using hh

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualAppellCoefficient_inner_eq_cumulant

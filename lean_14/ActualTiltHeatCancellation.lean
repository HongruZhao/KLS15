import ActualDampingDerivative
import ActualTiltLowOrder
import Mathlib

/-! The literal centered-basepoint heat cancellation (3.6), derived
from genuine theta Hessians and the genuine right damping derivative. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 3

 theorem integral_mul_norm_sq_eq_sum
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, f x*‖x‖^2 ∂μ) = ∑ i : Fin n, ∫ x, f x*(x i*x i) ∂μ := by
  obtain ⟨r,hr,hD,hD1⟩ := exists_common_local_exponential_domains hLC hf
  have hi (i : Fin n) : Integrable (fun x => f x*(x i*x i)) μ := by
    have hh := ((hD.mul_coordinate i).mul_coordinate i).integrable_tilt
      (show ‖(0 : Space n)‖ ≤ r by simpa using hr.le)
    convert hh using 1
    funext x
    simp only [inner_zero_left,Real.exp_zero,mul_one]
    ring
  have he (x : Space n) : f x*‖x‖^2 = ∑ i : Fin n, f x*(x i*x i) := by
    rw [EuclideanSpace.real_norm_sq_eq,Finset.mul_sum]
    simp only [pow_two]
  simp_rw [he]
  exact integral_finsetSum Finset.univ (fun i _ => hi i)

 theorem integral_norm_sq_of_isotropic (hiso : IsIsotropic μ) :
    (∫ x, ‖x‖^2 ∂μ) = (n : ℝ) := by
  have hi (i : Fin n) : Integrable (fun x : Space n => x i*x i) μ :=
    (hiso.memLp_coordinate i).integrable_mul (hiso.memLp_coordinate i)
  simp_rw [EuclideanSpace.real_norm_sq_eq,pow_two]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp [hiso.integral_coordinate_mul]

 theorem coordinateLaplacian_normalized_tilt_zero_of_isotropic
    (hLC : measureLogConcave μ) (hiso : IsIsotropic μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    coordinateLaplacian (fun z => ∫ x, f x ∂exponentialTilt μ z) 0 =
      (∫ x, f x*‖x‖^2 ∂μ)-(n : ℝ)*(∫ x, f x ∂μ) := by
  unfold coordinateLaplacian
  simp_rw [coordinateHessian_normalized_tilt_zero_of_isotropic hLC hiso hf]
  simp only [ite_true,mul_one]
  rw [Finset.sum_sub_distrib,← integral_mul_norm_sq_eq_sum hLC hf]
  simp

/-- Exact (3.6) at an isotropic centered basepoint: the one-sided damping
derivative is minus one half the true theta Laplacian. -/
 theorem hasDerivWithinAt_damping_eq_neg_half_laplacian
    (hLC : measureLogConcave μ) (hiso : IsIsotropic μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    HasDerivWithinAt
      (fun s : ℝ => ∫ x, f x ∂μ.tilted (fun x => -s*(‖x‖^2/2)))
      (-(1/2 : ℝ)*coordinateLaplacian (fun z => ∫ x, f x ∂exponentialTilt μ z) 0)
      (Ici 0) 0 := by
  have hd := hasDerivWithinAt_quadratic_damping_average hLC hf
  have he : (∫ x, f x*(‖x‖^2/2) ∂μ) = (∫ x, f x*‖x‖^2 ∂μ)/2 := by
    rw [← integral_div]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  rw [he,integral_div,integral_norm_sq_of_isotropic hiso] at hd
  convert hd using 1
  rw [coordinateLaplacian_normalized_tilt_zero_of_isotropic hLC hiso hf]
  ring

 def actualHeatGenerator (μ : Measure (Space n)) (f : Space n → ℝ) : ℝ :=
  derivWithin (fun s : ℝ => ∫ x, f x ∂μ.tilted (fun x => -s*(‖x‖^2/2))) (Ici 0) 0+
    (1/2 : ℝ)*coordinateLaplacian (fun z => ∫ x, f x ∂exponentialTilt μ z) 0

 theorem actualHeatGenerator_eq_zero (hLC : measureLogConcave μ) (hiso : IsIsotropic μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) : actualHeatGenerator μ f = 0 := by
  unfold actualHeatGenerator
  rw [(hasDerivWithinAt_damping_eq_neg_half_laplacian hLC hiso hf).derivWithin
    (uniqueDiffWithinAt_Ici (0 : ℝ))]
  ring

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.hasDerivWithinAt_damping_eq_neg_half_laplacian
#print axioms KLS.DeterministicBridgeIntegration.actualHeatGenerator_eq_zero

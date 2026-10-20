import ActualMixedDampingCommutation
import ActualTiltLowOrder
import Mathlib

/-! The genuine normalized heat identity on a theta neighborhood.
Unlike the centered basepoint cancellation, this identity can be
differentiated in theta to obtain all-order coefficient drift. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

 theorem coordinateHessian_congr_eventuallyEq
    {f g : Space n → ℝ} {z : Space n} (he : f =ᶠ[𝓝 z] g) (i j : Fin n) :
    coordinateHessian f z i j = coordinateHessian g z i j := by
  have he' : coordinateDerivative f j =ᶠ[𝓝 z] coordinateDerivative g j :=
    he.fderiv.fun_comp (fun L => L (EuclideanSpace.single j 1))
  exact congrArg (fun L : Space n →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) he'.fderiv_eq

 theorem coordinateLaplacian_congr_eventuallyEq
    {f g : Space n → ℝ} {z : Space n} (he : f =ᶠ[𝓝 z] g) :
    coordinateLaplacian f z = coordinateLaplacian g z := by
  apply Finset.sum_congr rfl
  intro i hi
  exact coordinateHessian_congr_eventuallyEq he i i

 theorem coordinateLaplacian_mul_of_contDiffAt
    {f g : Space n → ℝ} {z : Space n}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    coordinateLaplacian (fun y => f y*g y) z =
      coordinateLaplacian f z*g z+
        2*(∑ i, coordinateDerivative f i z*coordinateDerivative g i z)+
        f z*coordinateLaplacian g z := by
  simp only [coordinateLaplacian,coordinateHessian_mul_of_contDiffAt hf hg,
    Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

 theorem coordinateHessian_tiltNumerator_of_local
    {μ : Measure (Space n)} {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r) {z : Space n} (hz : ‖z‖ < r) (i j : Fin n) :
    coordinateHessian (tiltNumerator μ (fun _ => 0) f) z i j =
      tiltNumerator μ (fun _ => 0) (fun x => f x*(x i*x j)) z := by
  have he := directionalWordDerivative_tiltNumerator_of_local hf
    [EuclideanSpace.single i 1,EuclideanSpace.single j 1] hz
  unfold coordinateHessian coordinateDerivative
  simpa only [directionalWordDerivative,
    innerWordMonomial,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    EuclideanSpace.inner_single_right,RCLike.conj_to_real,one_mul,mul_one] using he

 theorem coordinateLaplacian_tiltNumerator_eq_quadratic
    {μ : Measure (Space n)} {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r) {z : Space n} (hz : ‖z‖ < r) :
    coordinateLaplacian (tiltNumerator μ (fun _ => 0) f) z =
      2*tiltNumerator μ (fun _ => 0) (fun x => f x*(‖x‖^2/2)) z := by
  have hi (i : Fin n) : Integrable
      (fun x => f x*(x i*x i)*Real.exp (inner ℝ z x)) μ := by
    convert (((hf.mul_coordinate i).mul_coordinate i).integrable_tilt hz.le) using 1
    funext x
    ring
  simp only [coordinateLaplacian,coordinateHessian_tiltNumerator_of_local hf hz,
    tiltNumerator,zero_add]
  rw [← integral_finsetSum Finset.univ (fun i _ => hi i),← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ = ∑ i : Fin n, (f x*Real.exp (inner ℝ z x))*(x i)^2 := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (f x*Real.exp (inner ℝ z x))*(∑ i : Fin n, (x i)^2) :=
        (Finset.mul_sum _ _ _).symm
      _ = _ := by ring

 def actualTiltMeanCoordinate (μ : Measure (Space n)) (i : Fin n) (z : Space n) : ℝ :=
  actualDampedAverage μ (fun x => x i) 0 z

/-- Literal (3.6) on a whole local theta ball, with the proved damping
response in place of a postulated parameter derivative. -/
 theorem actualDampingResponse_add_half_laplacian
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r)
    (h1 : LocalNormExponentialDomain μ (fun _ => 1) r)
    {z : Space n} (hz : ‖z‖ < r) :
    actualDampingResponse μ f z+
        (1/2 : ℝ)*coordinateLaplacian (actualDampedAverage μ f 0) z =
      -∑ i : Fin n, actualTiltMeanCoordinate μ i z*
        coordinateDerivative (actualDampedAverage μ f 0) i z := by
  let N := tiltNumerator μ (fun _ => 0) f
  let Z := tiltNumerator μ (fun _ => 0) (fun _ => 1)
  let A := actualDampedAverage μ f 0
  have hNz : ContDiffAt ℝ 2 N z :=
    ((contDiffOn_tiltNumerator_of_localNormExponentialDomain hf).contDiffAt
      (isOpen_ball.mem_nhds (by simpa using hz))).of_le (by simp)
  have hZz : ContDiffAt ℝ 2 Z z :=
    ((contDiffOn_tiltNumerator_of_localNormExponentialDomain h1).contDiffAt
      (isOpen_ball.mem_nhds (by simpa using hz))).of_le (by simp)
  have hAz : ContDiffAt ℝ 2 A z :=
    ((contDiffOn_actualDampedAverage hf h1 (show (0 : ℝ) ≤ 0 from le_rfl)).contDiffAt
      (isOpen_ball.mem_nhds (by simpa using hz))).of_le (by simp)
  have hzpos : 0 < Z z := by
    simpa only [Z,tiltNumerator,zero_add,one_mul] using
      integral_exp_pos (by simpa only [one_mul] using h1.integrable_tilt hz.le)
  have hAZ : (fun y => A y*Z y) =ᶠ[𝓝 z] N := by
    filter_upwards [hZz.continuousAt.eventually_ne hzpos.ne'] with y hy
    change actualDampedAverage μ f 0 y*Z y = N y
    simp only [actualDampedAverage,actualDampedNumerator,neg_zero,zero_mul,
      Real.exp_zero,mul_one,N,Z,tiltNumerator,zero_add]
    exact div_mul_cancel₀ _ (by simpa only [Z,tiltNumerator,zero_add] using hy)
  have hprod := coordinateLaplacian_mul_of_contDiffAt hAz hZz
  rw [coordinateLaplacian_congr_eventuallyEq hAZ] at hprod
  have hLN := coordinateLaplacian_tiltNumerator_eq_quadratic hf hz
  have hLZ := coordinateLaplacian_tiltNumerator_eq_quadratic h1 hz
  have hmean (i : Fin n) : actualTiltMeanCoordinate μ i z = coordinateDerivative Z i z/Z z := by
    have hd := fderiv_tiltNumerator_apply_inner_of_local h1 hz (EuclideanSpace.single i 1)
    change actualDampedAverage μ (fun x => x i) 0 z =
      fderiv ℝ (tiltNumerator μ (fun _ => 0) (fun _ => 1)) z (EuclideanSpace.single i 1)/Z z
    rw [hd]
    simp [actualDampedAverage,actualDampedNumerator,tiltNumerator,Z,EuclideanSpace.inner_single_right]
  simp_rw [hmean,div_mul_eq_mul_div,← Finset.sum_div]
  have hscomm : (∑ i : Fin n, coordinateDerivative Z i z*coordinateDerivative A i z) =
      ∑ i : Fin n, coordinateDerivative A i z*coordinateDerivative Z i z := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  change actualDampingResponse μ f z+1*coordinateLaplacian A z/2 = _
  rw [hscomm]
  have hR : actualDampingResponse μ f z =
      -tiltNumerator μ (fun _ => 0) (fun x => f x*(‖x‖^2/2)) z/Z z+
        A z*(tiltNumerator μ (fun _ => 0) (fun x => ‖x‖^2/2) z/Z z) := by
    simp [actualDampingResponse,actualDampedAverage,actualDampedNumerator,Z,A,tiltNumerator]
    ring
  rw [hR]
  simp only [one_mul] at hLZ
  change coordinateLaplacian N z = _ at hLN
  change coordinateLaplacian Z z = _ at hLZ
  have hNr : tiltNumerator μ (fun _ => 0) (fun x => f x*(‖x‖^2/2)) z =
      coordinateLaplacian N z/2 := by linarith
  have hZr : tiltNumerator μ (fun _ => 0) (fun x => ‖x‖^2/2) z =
      coordinateLaplacian Z z/2 := by linarith
  rw [hNr,hZr]
  field_simp [hzpos.ne']
  nlinarith [hprod]

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualDampingResponse_add_half_laplacian

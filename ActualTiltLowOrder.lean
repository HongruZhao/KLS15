import ActualLawTiltSmooth
import KLS.IsotropicSecondTaylor
import KLS.LocalTiltNumeratorMoments
import Mathlib

/-! Actual full-class first and second normalized tilt derivatives.
Every derivative is local; no global exponential domain is required. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix Filter Set Metric
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n : ℕ}
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

 theorem coordinateHessian_mul_of_contDiffAt {f g : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (i j : Fin n) :
    coordinateHessian (fun y => f y*g y) x i j =
      coordinateHessian f x i j*g x+coordinateDerivative f j x*coordinateDerivative g i x+
        (coordinateDerivative f i x*coordinateDerivative g j x+f x*coordinateHessian g x i j) := by
  have hdf : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hdg : DifferentiableAt ℝ g x := hg.differentiableAt (by norm_num)
  have hf' : DifferentiableAt ℝ (coordinateDerivative f j) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hg' : DifferentiableAt ℝ (coordinateDerivative g j) x :=
    ((hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have he : coordinateDerivative (fun y => f y*g y) j =ᶠ[𝓝 x]
      (fun y => coordinateDerivative f j y*g y+f y*coordinateDerivative g j y) := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with y hyf hyg
    exact coordinateDerivative_mul (hyf.differentiableAt (by norm_num))
      (hyg.differentiableAt (by norm_num)) j
  change (fderiv ℝ (coordinateDerivative (fun y => f y*g y) j) x) (EuclideanSpace.single i 1) = _
  rw [he.fderiv_eq]
  change coordinateDerivative ((fun y => coordinateDerivative f j y*g y)+
      (fun y => f y*coordinateDerivative g j y)) i x = _
  rw [coordinateDerivative_add (f := fun y => coordinateDerivative f j y*g y)
      (g := fun y => f y*coordinateDerivative g j y) (hf'.mul hdg) (hdf.mul hg'),
    coordinateDerivative_mul hf' hdg,coordinateDerivative_mul hdf hg']
  rfl

 theorem coordinateHessian_tiltNumerator_zero_of_local
    {μ : Measure (Space n)} {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r) (hr : 0 < r) (i j : Fin n) :
    coordinateHessian (tiltNumerator μ (fun _ => 0) f) 0 i j =
      ∫ x, f x*(x i*x j) ∂μ := by
  have hs := (contDiffOn_tiltNumerator_of_localNormExponentialDomain hf).contDiffAt
    (isOpen_ball.mem_nhds (by simpa using hr : (0 : Space n) ∈ ball 0 r))
  have hd := ((hs.of_le (by simp) : ContDiffAt ℝ 2 _ _).fderiv_right
    (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hh := iteratedFDeriv_tiltNumerator_moment_of_local hf
    (by simpa using hr : ‖(0 : Space n)‖ < r)
    ![EuclideanSpace.single i 1,EuclideanSpace.single j 1]
  rw [coordinateHessian_eq_fderiv_fderiv hd]
  simpa only [iteratedFDeriv_two_apply,Fin.isValue,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.head_cons,Fin.prod_univ_two,
    EuclideanSpace.inner_single_right,RCLike.conj_to_real,one_mul,
    inner_zero_left,Real.exp_zero,mul_one] using hh

 theorem coordinateDerivative_tiltNumerator_zero_of_local
    {μ : Measure (Space n)} {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r) (hr : 0 < r) (i : Fin n) :
    coordinateDerivative (tiltNumerator μ (fun _ => 0) f) i 0 =
      ∫ x, f x*x i ∂μ := by
  unfold coordinateDerivative
  rw [(hasFDerivAt_tiltNumerator_coordinate_of_localNormExponentialDomain hf
    (by simpa using hr : ‖(0 : Space n)‖ < r)).fderiv]
  simp [tiltNumerator]

 theorem hasFDerivAt_normalized_tilt_average_zero_of_isotropic
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) (hiso : IsIsotropic μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    HasFDerivAt (fun z => ∫ x, f x ∂exponentialTilt μ z)
      (∑ i, (∫ x, f x*x i ∂μ) • (EuclideanSpace.proj i : Space n →L[ℝ] ℝ)) 0 := by
  obtain ⟨r,hr,hD,hD1⟩ := exists_common_local_exponential_domains hLC hf
  have hz : ‖(0 : Space n)‖ < r := by simpa using hr
  have hN := hasFDerivAt_tiltNumerator_coordinate_of_localNormExponentialDomain hD hz
  have hZ := hasFDerivAt_tiltNumerator_coordinate_of_localNormExponentialDomain hD1 hz
  have hzne : tiltNumerator μ (fun _ => 0) (fun _ => 1) 0 ≠ 0 := by simp [tiltNumerator]
  have hd := hN.mul ((hasDerivAt_inv hzne).comp_hasFDerivAt 0 hZ)
  have he (i : Fin n) : (∫ x, 1*x i ∂μ) = 0 := by simpa using hiso.integral_coordinate i
  convert hd using 1
  · funext z
    change tiltAverage μ (fun x => inner ℝ z x) f = _
    simp only [tiltAverage_eq_ratio,Pi.mul_apply,Function.comp_apply,
      tiltNumerator,tiltPartition,zero_add,one_mul,div_eq_mul_inv]
  · simp [tiltNumerator,hiso.integral_coordinate]

 theorem actualAppellCoefficient_one_of_isotropic
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) (hiso : IsIsotropic μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (a : Fin 1 → Fin n) :
    actualAppellCoefficient μ f 1 a = ∫ x, f x*x (a 0) ∂μ := by
  unfold actualAppellCoefficient
  rw [iteratedFDeriv_one_apply,
    (hasFDerivAt_normalized_tilt_average_zero_of_isotropic hLC hiso hf).fderiv]
  simp

 theorem coordinateHessian_normalized_tilt_zero_of_isotropic
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) (hiso : IsIsotropic μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (i j : Fin n) :
    coordinateHessian (fun z => ∫ x, f x ∂exponentialTilt μ z) 0 i j =
      (∫ x, f x*(x i*x j) ∂μ)-(∫ x, f x ∂μ)*(if i=j then 1 else 0) := by
  let N := tiltNumerator μ (fun _ => 0) f
  let Z := tiltNumerator μ (fun _ => 0) (fun _ => 1)
  let A := fun z => ∫ x, f x ∂exponentialTilt μ z
  obtain ⟨r,hr,hD,hD1⟩ := exists_common_local_exponential_domains hLC hf
  have hA : ContDiffAt ℝ 2 A 0 := (contDiffAt_normalized_tilt_average hLC hf).of_le (by simp)
  have hZ : ContDiffAt ℝ 2 Z 0 := by
    exact ((contDiffOn_tiltNumerator_of_localNormExponentialDomain hD1).contDiffAt
      (isOpen_ball.mem_nhds (by simpa using hr : (0 : Space n) ∈ ball 0 r))).of_le (by simp)
  have hN : ContDiffAt ℝ 2 N 0 := by
    exact ((contDiffOn_tiltNumerator_of_localNormExponentialDomain hD).contDiffAt
      (isOpen_ball.mem_nhds (by simpa using hr : (0 : Space n) ∈ ball 0 r))).of_le (by simp)
  have heq : (fun z => A z*Z z) =ᶠ[𝓝 0] N := by
    filter_upwards [ball_mem_nhds (0 : Space n) hr] with z hz
    have hz' : ‖z‖ ≤ r := (show ‖z‖ < r by simpa only [mem_ball,dist_zero_right] using hz).le
    have hzN : Z z ≠ 0 := by
      change (∫ x, 1*Real.exp (0+inner ℝ z x) ∂μ) ≠ 0
      simpa only [one_mul,zero_add] using
        (integral_exp_pos (by simpa only [one_mul] using hD1.integrable_tilt hz')).ne'
    change tiltAverage μ (fun x => inner ℝ z x) f*Z z = N z
    rw [tiltAverage_eq_ratio]
    simpa only [N,Z,tiltNumerator,tiltPartition,zero_add,one_mul] using div_mul_cancel₀ (N z) hzN
  have hHeq : coordinateHessian (fun z => A z*Z z) 0 i j = coordinateHessian N 0 i j := by
    have hdP := ((hA.mul hZ).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hdN := (hN.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    rw [coordinateHessian_eq_fderiv_fderiv hdP,coordinateHessian_eq_fderiv_fderiv hdN]
    have hh := congrArg (fun T => T ![EuclideanSpace.single i (1 : ℝ),EuclideanSpace.single j (1 : ℝ)])
      ((heq.iteratedFDeriv ℝ 2).eq_of_nhds)
    simpa only [iteratedFDeriv_two_apply,Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one] using hh
  have hZ0 : Z 0 = 1 := by simp [Z,tiltNumerator]
  have hDZ (k : Fin n) : coordinateDerivative Z k 0 = 0 := by
    rw [coordinateDerivative_tiltNumerator_zero_of_local hD1 hr]
    simpa using hiso.integral_coordinate k
  have hHZ : coordinateHessian Z 0 i j = if i=j then 1 else 0 := by
    rw [coordinateHessian_tiltNumerator_zero_of_local hD1 hr]
    simpa using hiso.integral_coordinate_mul i j
  have hn := coordinateHessian_tiltNumerator_zero_of_local hD hr i j
  have hp := coordinateHessian_mul_of_contDiffAt hA hZ i j
  rw [hHeq,hZ0,hDZ,hDZ,hHZ] at hp
  have hA0 : A 0 = ∫ x, f x ∂μ := by simp [A]
  change coordinateHessian A 0 i j = _
  change coordinateHessian N 0 i j = _ at hn
  rw [hn,hA0] at hp
  linarith

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualAppellCoefficient_one_of_isotropic
#print axioms KLS.DeterministicBridgeIntegration.coordinateHessian_normalized_tilt_zero_of_isotropic

import ActualAppellMultiplication
import ActualAppellQuadraticSeed

/-! Exact degree-three normalized tilt formula under the existing full-class
hypotheses. Coordinate multiplication requires a local exponential moment
domain, not an extra L² assumption on the multiplied test. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix Filter Set Metric
open scoped ContDiff Topology BigOperators
namespace KLSImprovement.CubicFormula
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
variable {n : ℕ}
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

theorem coordinateHessian_normalized_tilt_zero_of_local
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hiso : IsIsotropic μ) {f : Space n → ℝ} {r : ℝ}
    (hD : LocalNormExponentialDomain μ f r)
    (hD1 : LocalNormExponentialDomain μ (fun _ => 1) r)
    (hr : 0 < r) (i j : Fin n) :
    coordinateHessian (fun z => ∫ x, f x ∂exponentialTilt μ z) 0 i j =
      (∫ x, f x*(x i*x j) ∂μ)-(∫ x, f x ∂μ)*(if i=j then 1 else 0) := by
  let N := tiltNumerator μ (fun _ => 0) f
  let Z := tiltNumerator μ (fun _ => 0) (fun _ => 1)
  let A := fun z => ∫ x, f x ∂exponentialTilt μ z
  have hA : ContDiffAt ℝ 2 A 0 := by
    have hs := (contDiffOn_actualDampedAverage hD hD1 (show (0 : ℝ) ≤ 0 from le_rfl)).contDiffAt
      (isOpen_ball.mem_nhds (by simpa using hr : (0 : Space n) ∈ ball 0 r))
    rw [actualDampedAverage_zero_eq_tilt_average] at hs
    exact hs.of_le (by simp)
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


theorem actualAppellCoefficient_two_of_local
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hiso : IsIsotropic μ) {f : Space n → ℝ} {r : ℝ}
    (hD : LocalNormExponentialDomain μ f r)
    (hD1 : LocalNormExponentialDomain μ (fun _ => 1) r)
    (hr : 0 < r) (a : Fin 2 → Fin n) :
    actualAppellCoefficient μ f 2 a =
      (∫ x, f x*(x (a 0)*x (a 1)) ∂μ)
        -(∫ x,f x ∂μ)*(if a 0=a 1 then 1 else 0) := by
  have hs := (contDiffOn_actualDampedAverage hD hD1 (show (0 : ℝ) ≤ 0 from le_rfl)).contDiffAt
    (isOpen_ball.mem_nhds (by simpa using hr : (0 : Space n) ∈ ball 0 r))
  rw [actualDampedAverage_zero_eq_tilt_average] at hs
  have hd := ((hs.of_le (by simp) : ContDiffAt ℝ 2 _ _).fderiv_right
    (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [actualAppellCoefficient,iteratedFDeriv_two_apply,
    ←coordinateHessian_eq_fderiv_fderiv hd,
    coordinateHessian_normalized_tilt_zero_of_local hiso hD hD1 hr]

theorem actualAppellCoordinateLower_two
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) (hiso : IsIsotropic μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (i j k : Fin n) :
    actualAppellCoordinateLower μ f i ![EuclideanSpace.single j 1,EuclideanSpace.single k 1] =
      (∫ x,x i*x j*x k ∂μ)*(∫ x,f x ∂μ)
      +(if i=k then 1 else 0)*(∫ x,f x*x j ∂μ)
      +(if i=j then 1 else 0)*(∫ x,f x*x k ∂μ) := by
  classical
  obtain ⟨r,hr,hD,h1D⟩ := exists_common_local_exponential_domains hLC hf
  let A := actualDampedAverage μ f 0
  let M := actualTiltMeanCoordinate μ i
  let m : Fin 2→Space n := ![EuclideanSpace.single j 1,EuclideanSpace.single k 1]
  have h0 : (0 : Space n)∈ball 0 r := by simpa using hr
  have hA := contDiffOn_actualDampedAverage hD h1D (show (0 : ℝ)≤0 from le_rfl)
  have hMi : LocalNormExponentialDomain μ (fun x : Space n=>x i) r := by
    simpa only [one_mul] using h1D.mul_coordinate i
  have hM := contDiffOn_actualDampedAverage hMi h1D (show (0 : ℝ)≤0 from le_rfl)
  change ContDiffOn ℝ (⊤ : ℕ∞) M (ball 0 r) at hM
  change ContDiffOn ℝ (⊤ : ℕ∞) A (ball 0 r) at hA
  have hsecond : iteratedFDeriv ℝ 2 (fun z=>M z*A z) 0 m =
      actualAppellCoordinateLower μ f i m := by
    have hw : directionalWordDerivative (fun z=>M z*A z) (List.ofFn m) 0 =
        iteratedFDeriv ℝ 2 (fun z=>M z*A z) 0 m :=
      local_word_ofFn isOpen_ball (hM.mul hA) m h0
    rw [←hw,local_word_product_masks isOpen_ball hM hA m h0]
    unfold actualAppellCoordinateLower
    rw [←(maskFinsetEquiv 2).sum_comp]
    apply Finset.sum_congr rfl
    intro s hs
    change _ = listCumulant μ
      (maskedDirections m (fun q=>decide (q∈maskSet s))++[EuclideanSpace.single i 1])*
        directionalWordDerivative (actualDampedAverage μ f 0)
          (maskedDirections m (fun q=>!(decide (q∈maskSet s)))) 0
    simp only [mem_maskSet,Bool.decide_coe]
    exact congrArg (fun c : ℝ=>c*directionalWordDerivative A
      (maskedDirections m (fun q=>!(s q))) 0)
      (actualTiltMean_word_eq_cumulant hLC i (maskedDirections m s))
  have hMa : ContDiffAt ℝ 2 M 0 := (hM.contDiffAt (isOpen_ball.mem_nhds h0)).of_le (by simp)
  have hAa : ContDiffAt ℝ 2 A 0 := (hA.contDiffAt (isOpen_ball.mem_nhds h0)).of_le (by simp)
  have hdm := ((hMa.mul hAa).fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hH : coordinateHessian (fun z=>M z*A z) 0 j k =
      actualAppellCoordinateLower μ f i m := by
    rw [coordinateHessian_eq_fderiv_fderiv hdm]
    simpa only [iteratedFDeriv_two_apply,m,Fin.isValue,Matrix.cons_val_zero,
      Matrix.cons_val_one] using hsecond
  have hHM : coordinateHessian M 0 j k=∫ x,x i*x j*x k ∂μ := by
    change coordinateHessian (actualDampedAverage μ (fun x=>x i) 0) 0 j k = _
    rw [actualDampedAverage_zero_eq_tilt_average,
      coordinateHessian_normalized_tilt_zero_of_local hiso hMi h1D hr,
      hiso.integral_coordinate,zero_mul,sub_zero]
    apply integral_congr_ae
    exact .of_forall (fun x=>by ring)
  have hDM (l:Fin n) : coordinateDerivative M l 0=if i=l then 1 else 0 := by
    change directionalWordDerivative (actualTiltMeanCoordinate μ i) [EuclideanSpace.single l 1] 0 = _
    rw [actualTiltMean_singleton_of_isotropic hLC hiso]
    simp
  have hDA (l:Fin n) : coordinateDerivative A l 0=∫ x,f x*x l ∂μ := by
    change coordinateDerivative (actualDampedAverage μ f 0) l 0 = _
    rw [actualDampedAverage_zero_eq_tilt_average]
    unfold coordinateDerivative
    rw [(hasFDerivAt_normalized_tilt_average_zero_of_isotropic hLC hiso hf).fderiv]
    simp
  have hM0 : M 0=0 := actualTiltMean_zero_of_isotropic hiso i
  have hA0 : A 0=∫ x,f x ∂μ := by
    change actualDampedAverage μ f 0 0 = _
    rw [actualDampedAverage_zero_eq_tilt_average]
    simp
  rw [←hH,coordinateHessian_mul_of_contDiffAt hMa hAa,hHM,hDM,hDM,hDA,hDA,hM0,hA0]
  ring

/-- The actual cubic coefficient, with every centering and covariance term.
The multiplied test is not assumed to lie in L². -/
theorem actualAppellCoefficient_three_moment_formula
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) (hiso : IsIsotropic μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (i j k:Fin n) :
    actualAppellCoefficient μ f 3 ![i,j,k] =
      (∫ x,x i*f x*(x j*x k) ∂μ)
      -(∫ x,x i*f x ∂μ)*(if j=k then 1 else 0)
      -(if i=k then 1 else 0)*(∫ x,f x*x j ∂μ)
      -(if i=j then 1 else 0)*(∫ x,f x*x k ∂μ)
      -(∫ x,x i*x j*x k ∂μ)*(∫ x,f x ∂μ) := by
  obtain ⟨r,hr,hD,h1D⟩ := exists_common_local_exponential_domains hLC hf
  have hDi : LocalNormExponentialDomain μ (fun x=>x i*f x) r := by
    simpa only [mul_comm] using hD.mul_coordinate i
  have hc := actualAppellCoefficient_coordinate_mul hLC hf i ![j,k]
  have ht := actualAppellCoefficient_two_of_local hiso hDi h1D hr ![j,k]
  have he : (fun q : Fin 2=>EuclideanSpace.single (![j,k] q) (1:ℝ)) =
      ![EuclideanSpace.single j 1,EuclideanSpace.single k 1] := by
    funext q;fin_cases q <;>simp
  rw [he,actualAppellCoordinateLower_two hLC hiso hf] at hc
  simp only [Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one] at ht
  change _=actualAppellCoefficient μ f 3 ![i,j,k]+_ at hc
  rw [ht] at hc
  linarith

end KLSImprovement.CubicFormula
#print axioms KLSImprovement.CubicFormula.coordinateHessian_normalized_tilt_zero_of_local
#print axioms KLSImprovement.CubicFormula.actualAppellCoefficient_two_of_local
#print axioms KLSImprovement.CubicFormula.actualAppellCoordinateLower_two
#print axioms KLSImprovement.CubicFormula.actualAppellCoefficient_three_moment_formula

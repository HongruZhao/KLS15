import ActualAppellCumulantDrift
import ActualTiltWhitening

/-! Actual covariance variation of the genuine tilted and damped law. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace Set Filter Metric Matrix
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem coordinateDerivative_actualDampedAverage
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] {r : ℝ}
    {f : Space n → ℝ} (hf : LocalNormExponentialDomain μ f r)
    (h1 : LocalNormExponentialDomain μ (fun _ => 1) r)
    {s : ℝ} (hs : 0 ≤ s) {z : Space n} (hz : ‖z‖ < r) (j : Fin n) :
    coordinateDerivative (actualDampedAverage μ f s) j z =
      actualDampedAverage μ (fun x => f x*x j) s z-
        actualDampedAverage μ f s z*actualDampedAverage μ (fun x => x j) s z := by
  let N := actualDampedNumerator μ f s
  let Z := actualDampedNumerator μ (fun _ => 1) s
  have hN : HasFDerivAt N
      (∑ i, actualDampedNumerator μ (fun x => f x*x i) s z •
        (EuclideanSpace.proj i : Space n →L[ℝ] ℝ)) z := by
    convert hasFDerivAt_tiltNumerator_coordinate_of_localNormExponentialDomain
      (LocalNormExponentialDomain.mul_nonneg_damping hf hs) hz using 1
    · funext w
      simp only [N,actualDampedNumerator,tiltNumerator,zero_add]
    · congr 1
      funext i
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [actualDampedNumerator,tiltNumerator,zero_add]
        ring
  have hZ : HasFDerivAt Z
      (∑ i, actualDampedNumerator μ (fun x => x i) s z •
        (EuclideanSpace.proj i : Space n →L[ℝ] ℝ)) z := by
    convert hasFDerivAt_tiltNumerator_coordinate_of_localNormExponentialDomain
      (LocalNormExponentialDomain.mul_nonneg_damping h1 hs) hz using 1
    · funext w
      simp only [Z,actualDampedNumerator,tiltNumerator,zero_add]
    · congr 1
      funext i
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [actualDampedNumerator,tiltNumerator,zero_add]
        ring
  have hZn : Z z ≠ 0 := (actualDampedNumerator_one_pos h1 hs hz.le).ne'
  have hd := hN.mul ((hasDerivAt_inv hZn).comp_hasFDerivAt z hZ)
  change HasFDerivAt (fun w => N w*(Z w)⁻¹) _ z at hd
  have he : actualDampedAverage μ f s = fun w => N w*(Z w)⁻¹ := by
    funext w
    simp only [actualDampedAverage,N,Z,div_eq_mul_inv]
  rw [he]
  unfold coordinateDerivative
  rw [hd.fderiv]
  simp [actualDampedAverage,N,Z,div_eq_mul_inv,inv_pow,pow_two]
  ring

 def actualCovarianceField (μ : Measure (Space n)) (s : ℝ) (z : Space n) :
    Matrix (Fin n) (Fin n) ℝ := covarianceMatrix (actualDampedTiltLaw μ z s)

 theorem actualCovarianceField_eq_mean_derivative
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) {r : ℝ}
    (h1 : LocalNormExponentialDomain μ (fun _ => 1) r)
    {s : ℝ} (hs : 0 ≤ s) {z : Space n} (hz : ‖z‖ < r) (i j : Fin n) :
    actualCovarianceField μ s z i j =
      coordinateDerivative (actualDampedAverage μ (fun x => x i) s) j z := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  let ν := actualDampedTiltLaw μ z s
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_tilted
    (integrable_exp_actualDampedExponent h1 hz.le hs)
  have hLC : measureLogConcave ν := actualDampedTiltLaw_logConcave hμ z hs
  have hid : MemLp (fun x : Space n => x) 2 ν := logConcave_memLp_id hLC
  have hi : MemLp (fun x : Space n => x i) 2 ν := hid.eval_piLp i
  have hj : MemLp (fun x : Space n => x j) 2 ν := hid.eval_piLp j
  have hxi : LocalNormExponentialDomain μ (fun x : Space n => x i) r := by
    simpa only [one_mul] using h1.mul_coordinate i
  rw [coordinateDerivative_actualDampedAverage hxi h1 hs hz]
  simp_rw [actualDampedAverage_eq_integral]
  exact (covarianceMatrix_apply hid i j).trans (covariance_eq_sub hi hj)

 theorem actualCovarianceField_damping_eq_mixed
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) {r : ℝ}
    (h1 : LocalNormExponentialDomain μ (fun _ => 1) r) (hr : 0 < r)
    {s : ℝ} (hs : 0 ≤ s) (i j : Fin n) :
    actualCovarianceField μ s 0 i j =
      actualDampedMixedJet μ (fun x => x i) 1 s (fun _ => EuclideanSpace.single j 1) := by
  rw [actualCovarianceField_eq_mean_derivative hμ h1 hs (by simpa using hr)]
  simp only [actualDampedMixedJet,iteratedFDeriv_one_apply,coordinateDerivative]

 theorem actualCovarianceField_zero
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) : actualCovarianceField μ 0 0 = 1 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  ext i j
  have hzero : actualDampedTiltLaw μ 0 0 = μ := by
    unfold actualDampedTiltLaw
    simp
  rw [actualCovarianceField,hzero,covarianceMatrix_apply hμ.isotropic.memLp_id,
    covariance_eq_sub (hμ.isotropic.memLp_coordinate i) (hμ.isotropic.memLp_coordinate j)]
  simp only [Pi.mul_apply,hμ.isotropic.integral_coordinate_mul,
    hμ.isotropic.integral_coordinate,zero_mul,sub_zero,Matrix.one_apply]

 theorem hasDerivWithinAt_actualCovarianceField_damping
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) (i j : Fin n) :
    HasDerivWithinAt (fun s : ℝ => actualCovarianceField μ s 0 i j)
      (iteratedFDeriv ℝ 1 (actualDampingResponse μ (fun x => x i)) 0
        (fun _ => EuclideanSpace.single j 1)) (Ici 0) 0 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨r,hr,h1⟩ := hμ.logConcave.exists_localNormExponentialDomain_one
  have he : EqOn (fun s : ℝ => actualCovarianceField μ s 0 i j)
      (fun s => actualDampedMixedJet μ (fun x => x i) 1 s
        (fun _ => EuclideanSpace.single j 1)) (Ici 0) := by
    intro s hs
    exact actualCovarianceField_damping_eq_mixed hμ h1 hr hs i j
  exact (hasDerivWithinAt_actualDampedMixedJet_response hμ.logConcave
    (hμ.isotropic.memLp_coordinate i) 1 (fun _ => EuclideanSpace.single j 1)).congr_of_mem
      he (by simp)

 theorem contDiffOn_actualCovarianceField_theta
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) {r : ℝ}
    (h1 : LocalNormExponentialDomain μ (fun _ => 1) r) {s : ℝ} (hs : 0 ≤ s) :
    ContDiffOn ℝ (⊤ : ℕ∞) (actualCovarianceField μ s) (ball 0 r) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  have hi : LocalNormExponentialDomain μ (fun x : Space n => x i) r := by
    simpa only [one_mul] using h1.mul_coordinate i
  have hA := contDiffOn_actualDampedAverage hi h1 hs
  exact (contDiffOn_word_of_isOpen isOpen_ball hA [EuclideanSpace.single j 1]).congr
    (fun z hz => actualCovarianceField_eq_mean_derivative hμ h1 hs
      (by simpa only [mem_ball,dist_zero_right] using hz) i j)

 theorem contDiffAt_actualCovarianceField_theta
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (actualCovarianceField μ 0) 0 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨r,hr,h1⟩ := hμ.logConcave.exists_localNormExponentialDomain_one
  exact (contDiffOn_actualCovarianceField_theta hμ h1 (show (0 : ℝ) ≤ 0 from le_rfl)).contDiffAt
    (isOpen_ball.mem_nhds (by simpa using hr))

 theorem coordinateLaplacian_coordinateDerivative_local
    {f : Space n → ℝ} {r : ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (ball 0 r))
    (hr : 0 < r) (j : Fin n) :
    coordinateLaplacian (coordinateDerivative f j) 0 =
      ∑ k : Fin n, iteratedFDeriv ℝ 3 f 0
        (Fin.cons (EuclideanSpace.single k 1)
          (Fin.cons (EuclideanSpace.single k 1) (fun _ : Fin 1 => EuclideanSpace.single j 1))) := by
  unfold coordinateLaplacian
  apply Finset.sum_congr rfl
  intro k hk
  change directionalWordDerivative f
      [EuclideanSpace.single k 1,EuclideanSpace.single k 1,EuclideanSpace.single j 1] 0 = _
  simpa only [List.ofFn_cons,List.ofFn_const,List.replicate_one] using
    local_word_ofFn isOpen_ball hf
      (Fin.cons (EuclideanSpace.single k 1)
        (Fin.cons (EuclideanSpace.single k 1) (fun _ : Fin 1 => EuclideanSpace.single j 1)))
      (by simpa using hr : (0 : Space n) ∈ ball 0 r)

 theorem actualAppellLowerDrift_one (μ : Measure (Space n)) (f : Space n → ℝ)
    (m : Fin 1 → Space n) : actualAppellLowerDrift μ f 1 m = 0 := by
  unfold actualAppellLowerDrift
  apply Finset.sum_eq_zero
  intro S hS
  have hc : S.card ≤ 1 := by simpa using S.card_le_univ
  have hn : ¬2 ≤ S.card := by omega
  simp only [hn,ite_false]

 def actualCovarianceHeatGenerator (μ : Measure (Space n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => derivWithin (fun s : ℝ => actualCovarianceField μ s 0 i j) (Ici 0) 0+
    (1/2 : ℝ)*coordinateLaplacian (fun z => actualCovarianceField μ 0 z i j) 0

 /-- Literal (3.9): the genuine centered isotropic covariance has heat
 drift −I. The damping derivative is right-sided and has already been proved. -/
 theorem actualCovarianceHeatGenerator_eq_neg_one
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    actualCovarianceHeatGenerator μ = -1 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨r,hr,h1⟩ := hμ.logConcave.exists_localNormExponentialDomain_one
  ext i j
  have hi : LocalNormExponentialDomain μ (fun x : Space n => x i) r := by
    simpa only [one_mul] using h1.mul_coordinate i
  have hA := contDiffOn_actualDampedAverage hi h1 (show (0 : ℝ) ≤ 0 from le_rfl)
  have he : (fun z => actualCovarianceField μ 0 z i j) =ᶠ[𝓝 (0 : Space n)]
      coordinateDerivative (actualDampedAverage μ (fun x => x i) 0) j := by
    filter_upwards [ball_mem_nhds (0 : Space n) hr] with z hz
    exact actualCovarianceField_eq_mean_derivative hμ h1 (by simp)
      (by simpa only [mem_ball,dist_zero_right] using hz) i j
  have hd : derivWithin (fun s : ℝ => actualCovarianceField μ s 0 i j) (Ici 0) 0 =
      derivWithin (fun s : ℝ => actualDampedMixedJet μ (fun x => x i) 1 s
        (fun _ => EuclideanSpace.single j 1)) (Ici 0) 0 := by
    apply derivWithin_congr
    · intro s hs
      exact actualCovarianceField_damping_eq_mixed hμ h1 hr hs i j
    · exact actualCovarianceField_damping_eq_mixed hμ h1 hr (by simp) i j
  have hB : iteratedFDeriv ℝ 1 (actualDampedAverage μ (fun x => x i) 0) 0
      (fun _ => EuclideanSpace.single j 1) = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    change actualDampedMixedJet μ (fun x => x i) 1 0
      (fun _ => EuclideanSpace.single j 1) = _
    rw [← actualCovarianceField_damping_eq_mixed hμ h1 hr (by simp) i j,
      actualCovarianceField_zero hμ]
  have hg := actualAppellHeatCoefficientGenerator_eq_drift hμ.logConcave hμ.isotropic
    (hμ.isotropic.memLp_coordinate i) 1 (fun _ => EuclideanSpace.single j 1)
  rw [actualAppellLowerDrift_one,hB] at hg
  change _ = -((1 : Matrix (Fin n) (Fin n) ℝ) i j)
  unfold actualCovarianceHeatGenerator
  rw [hd,coordinateLaplacian_congr_eventuallyEq he,
    coordinateLaplacian_coordinateDerivative_local hA hr j]
  simpa only [actualAppellHeatCoefficientGenerator,Nat.cast_one,one_mul,sub_zero,
    neg_mul,one_mul] using hg

 theorem coordinateDerivative_actualCovarianceField
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) (i j k : Fin n) :
    coordinateDerivative (fun z => actualCovarianceField μ 0 z i j) k 0 =
      thirdCumulantMatrix μ (MomentMap.coordinateVector k) i j := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨r,hr,h1⟩ := hμ.logConcave.exists_localNormExponentialDomain_one
  have he : (fun z => actualCovarianceField μ 0 z i j) =ᶠ[𝓝 (0 : Space n)]
      coordinateDerivative (actualDampedAverage μ (fun x => x i) 0) j := by
    filter_upwards [ball_mem_nhds (0 : Space n) hr] with z hz
    exact actualCovarianceField_eq_mean_derivative hμ h1 (by simp)
      (by simpa only [mem_ball,dist_zero_right] using hz) i j
  unfold coordinateDerivative
  rw [he.fderiv_eq,actualDampedAverage_zero_eq_tilt_average]
  change coordinateHessian (fun z => ∫ x, x i ∂exponentialTilt μ z) 0 k j = _
  rw [coordinateHessian_normalized_tilt_zero_of_isotropic hμ.logConcave hμ.isotropic
    (hμ.isotropic.memLp_coordinate i),hμ.isotropic.integral_coordinate,zero_mul,sub_zero,
    thirdCumulantMatrix_coordinate_eq_cubic]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

 theorem hasDerivWithinAt_actualCovarianceField_damping_matrix
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    HasDerivWithinAt (fun s : ℝ => actualCovarianceField μ s 0)
      (fun i j => iteratedFDeriv ℝ 1 (actualDampingResponse μ (fun x => x i)) 0
        (fun _ => EuclideanSpace.single j 1)) (Ici 0) 0 := by
  apply hasDerivWithinAt_pi.mpr
  intro i
  apply hasDerivWithinAt_pi.mpr
  intro j
  exact hasDerivWithinAt_actualCovarianceField_damping hμ i j

 theorem fderiv_actualCovarianceField
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) (k : Fin n) :
    fderiv ℝ (actualCovarianceField μ 0) 0 (EuclideanSpace.single k 1) =
      thirdCumulantMatrix μ (MomentMap.coordinateVector k) := by
  have hd := (contDiffAt_actualCovarianceField_theta hμ).differentiableAt (by simp)
  ext i j
  have hdi := differentiableAt_pi.mp hd i
  have hi := fderiv_apply hd i
  have hij := fderiv_apply hdi j
  have he : fderiv ℝ (fun z => actualCovarianceField μ 0 z i j) 0 (EuclideanSpace.single k 1) =
      (fderiv ℝ (actualCovarianceField μ 0) 0 (EuclideanSpace.single k 1)) i j := by
    rw [hij,hi]
    rfl
  rw [← he]
  exact coordinateDerivative_actualCovarianceField hμ i j k

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualCovarianceField_eq_mean_derivative
#print axioms KLS.DeterministicBridgeIntegration.hasDerivWithinAt_actualCovarianceField_damping
#print axioms KLS.DeterministicBridgeIntegration.actualCovarianceHeatGenerator_eq_neg_one
#print axioms KLS.DeterministicBridgeIntegration.coordinateDerivative_actualCovarianceField
#print axioms KLS.DeterministicBridgeIntegration.fderiv_actualCovarianceField

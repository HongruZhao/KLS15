import ActualAppellCumulantDrift
import ActualTiltWhitening

/-! Genuine finite coordinate Appell fields for the actual varying law.
These wrappers assemble the already-proved scalar family derivatives. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric Matrix
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem actualDampedTiltLaw_zero_damping (μ : Measure (Space n)) (z : Space n) :
    actualDampedTiltLaw μ z 0 = exponentialTilt μ z := by
  unfold actualDampedTiltLaw exponentialTilt
  congr 1
  funext x
  simp

 def actualAppellField (μ : Measure (Space n)) (f : Space n → ℝ)
    (d : ℕ) (s : ℝ) (z : Space n) : (Fin d → Fin n) → ℝ :=
  actualAppellCoefficient (actualDampedTiltLaw μ z s) f d

 @[simp] theorem actualAppellField_zero (μ : Measure (Space n)) [IsProbabilityMeasure μ] (f : Space n → ℝ)
    (d : ℕ) : actualAppellField μ f d 0 0 = actualAppellCoefficient μ f d := by
  unfold actualAppellField
  rw [actualDampedTiltLaw_zero_damping,exponentialTilt_zero]

 theorem actualAppellField_theta_eq_jet
    {μ : Measure (Space n)} {r : ℝ}
    (h1 : LocalNormExponentialDomain μ (fun _ => 1) r)
    (f : Space n → ℝ) (d : ℕ) {z : Space n} (hz : ‖z‖ ≤ r)
    (a : Fin d → Fin n) :
    actualAppellField μ f d 0 z a = actualTiltJet μ f d z a := by
  unfold actualAppellField
  rw [actualDampedTiltLaw_zero_damping]
  apply actualAppellCoefficient_exponentialTilt
  simpa only [one_mul] using h1.integrable_tilt hz

 theorem contDiffOn_actualAppellField_theta
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] {r : ℝ}
    {f : Space n → ℝ} (hf : LocalNormExponentialDomain μ f r)
    (h1 : LocalNormExponentialDomain μ (fun _ => 1) r) (d : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (actualAppellField μ f d 0) (ball 0 r) := by
  have hA := contDiffOn_actualDampedAverage hf h1 (show (0 : ℝ) ≤ 0 from le_rfl)
  apply contDiffOn_pi.mpr
  intro a
  let m : Fin d → Space n := fun j => EuclideanSpace.single (a j) 1
  exact (contDiffOn_word_of_isOpen isOpen_ball hA (List.ofFn m)).congr fun z hz => by
    rw [actualAppellField_theta_eq_jet h1 f d
      (show ‖z‖ ≤ r from (by simpa only [mem_ball,dist_zero_right] using hz : ‖z‖ < r).le)]
    unfold actualTiltJet
    rw [← actualDampedAverage_zero_eq_tilt_average]
    exact (local_word_ofFn isOpen_ball hA m hz).symm

 theorem contDiffAt_actualAppellField_theta
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) (d : ℕ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (actualAppellField μ f d 0) 0 := by
  obtain ⟨r,hr,hD,h1⟩ := exists_common_local_exponential_domains hLC hf
  exact (contDiffOn_actualAppellField_theta hD h1 d).contDiffAt
    (isOpen_ball.mem_nhds (by simpa using hr))

 theorem hasDerivWithinAt_actualAppellField_damping
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) (d : ℕ) :
    HasDerivWithinAt (fun s : ℝ => actualAppellField μ f d s 0)
      (fun a => iteratedFDeriv ℝ d (actualDampingResponse μ f) 0
        (fun j => EuclideanSpace.single (a j) 1)) (Ici 0) 0 := by
  apply hasDerivWithinAt_pi.mpr
  intro a
  exact hasDerivWithinAt_actualAppellCoefficient_dampedLaw hLC hf d a

 theorem coordinateDerivative_actualAppellField
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (d : ℕ) (a : Fin d → Fin n) (i : Fin n) :
    coordinateDerivative (fun z => actualAppellField μ f d 0 z a) i 0 =
      actualAppellCoefficient μ f (d+1) (Fin.cons i a) := by
  obtain ⟨r,hr,hD,h1⟩ := exists_common_local_exponential_domains hLC hf
  have he : (fun z => actualAppellField μ f d 0 z a) =ᶠ[𝓝 (0 : Space n)]
      (fun z => actualTiltJet μ f d z a) := by
    filter_upwards [ball_mem_nhds (0 : Space n) hr] with z hz
    exact actualAppellField_theta_eq_jet h1 f d
      (show ‖z‖ ≤ r from (by simpa only [mem_ball,dist_zero_right] using hz : ‖z‖ < r).le) a
  unfold coordinateDerivative
  rw [he.fderiv_eq]
  have hd := hasDerivAt_actualTiltJet_coordinate hLC hf d a i
  have hdiff := (contDiffAt_actualAppellField_theta hLC hf d).differentiableAt (by simp)
  have hjet : DifferentiableAt ℝ (fun z => actualTiltJet μ f d z a) 0 :=
    ((differentiableAt_pi.mp hdiff a).congr_of_eventuallyEq he.symm)
  have hc := hjet.hasFDerivAt.comp_hasDerivAt_of_eq 0
    ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single i (1 : ℝ))) (by simp)
  simpa only [one_smul] using hd.unique hc |>.symm

 theorem coordinateHessian_actualAppellField
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (d : ℕ) (a : Fin d → Fin n) (i j : Fin n) :
    coordinateHessian (fun z => actualAppellField μ f d 0 z a) 0 i j =
      iteratedFDeriv ℝ (d+2) (actualDampedAverage μ f 0) 0
        (Fin.cons (EuclideanSpace.single i 1)
          (Fin.cons (EuclideanSpace.single j 1) (fun k => EuclideanSpace.single (a k) 1))) := by
  obtain ⟨r,hr,hD,h1⟩ := exists_common_local_exponential_domains hLC hf
  have hA := contDiffOn_actualDampedAverage hD h1 (show (0 : ℝ) ≤ 0 from le_rfl)
  let m : Fin d → Space n := fun k => EuclideanSpace.single (a k) 1
  have he : (fun z => actualAppellField μ f d 0 z a) =ᶠ[𝓝 (0 : Space n)]
      directionalWordDerivative (actualDampedAverage μ f 0) (List.ofFn m) := by
    filter_upwards [ball_mem_nhds (0 : Space n) hr] with z hz
    rw [actualAppellField_theta_eq_jet h1 f d
      (show ‖z‖ ≤ r from (by simpa only [mem_ball,dist_zero_right] using hz : ‖z‖ < r).le)]
    unfold actualTiltJet
    rw [← actualDampedAverage_zero_eq_tilt_average]
    exact (local_word_ofFn isOpen_ball hA m hz).symm
  rw [coordinateHessian_congr_eventuallyEq he]
  change directionalWordDerivative (actualDampedAverage μ f 0)
    (EuclideanSpace.single i 1::EuclideanSpace.single j 1::List.ofFn m) 0 = _
  simpa only [List.ofFn_cons] using local_word_ofFn isOpen_ball hA
    (Fin.cons (EuclideanSpace.single i 1) (Fin.cons (EuclideanSpace.single j 1) m))
    (by simpa using hr : (0 : Space n) ∈ ball 0 r)

 def actualAppellFieldHeatGenerator (μ : Measure (Space n)) (f : Space n → ℝ)
    (d : ℕ) : (Fin d → Fin n) → ℝ :=
  fun a => derivWithin (fun s : ℝ => actualAppellField μ f d s 0 a) (Ici 0) 0+
    (1/2 : ℝ)*coordinateLaplacian (fun z => actualAppellField μ f d 0 z a) 0

 def actualAppellLowerDriftTensor (μ : Measure (Space n)) (f : Space n → ℝ)
    (d : ℕ) : (Fin d → Fin n) → ℝ :=
  fun a => actualAppellLowerDrift μ f d (fun j => EuclideanSpace.single (a j) 1)

 theorem actualAppellFieldHeatGenerator_eq_drift
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (d : ℕ) :
    actualAppellFieldHeatGenerator μ f d =
      -((d : ℝ) • actualAppellCoefficient μ f d+actualAppellLowerDriftTensor μ f d) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  funext a
  have hd : derivWithin (fun s : ℝ => actualAppellField μ f d s 0 a) (Ici 0) 0 =
      derivWithin (fun s : ℝ => actualDampedMixedJet μ f d s
        (fun j => EuclideanSpace.single (a j) 1)) (Ici 0) 0 := by
    apply derivWithin_congr
    · intro s hs
      exact actualAppellCoefficient_dampedLaw_eq_mixed hs f d a
    · exact actualAppellCoefficient_dampedLaw_eq_mixed (by simp) f d a
  have hL : coordinateLaplacian (fun z => actualAppellField μ f d 0 z a) 0 =
      ∑ i : Fin n, iteratedFDeriv ℝ (d+2) (actualDampedAverage μ f 0) 0
        (Fin.cons (EuclideanSpace.single i 1)
          (Fin.cons (EuclideanSpace.single i 1) (fun j => EuclideanSpace.single (a j) 1))) := by
    unfold coordinateLaplacian
    exact Finset.sum_congr rfl fun i hi => coordinateHessian_actualAppellField hμ.logConcave hf d a i i
  have hg := actualAppellHeatCoefficientGenerator_eq_drift hμ.logConcave hμ.isotropic hf d
    (fun j => EuclideanSpace.single (a j) 1)
  unfold actualAppellFieldHeatGenerator
  rw [hd,hL]
  change actualAppellHeatCoefficientGenerator μ f d (fun j => EuclideanSpace.single (a j) 1) = _
  rw [hg]
  rw [actualDampedAverage_zero_eq_tilt_average]
  change -(d : ℝ)*actualAppellCoefficient μ f d a-actualAppellLowerDriftTensor μ f d a = _
  simp only [Pi.neg_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.contDiffAt_actualAppellField_theta
#print axioms KLS.DeterministicBridgeIntegration.hasDerivWithinAt_actualAppellField_damping
#print axioms KLS.DeterministicBridgeIntegration.coordinateDerivative_actualAppellField
#print axioms KLS.DeterministicBridgeIntegration.actualAppellFieldHeatGenerator_eq_drift

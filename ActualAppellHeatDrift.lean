import ActualLocalHeatPDE
import LocalWordLeibniz
import Mathlib

/-! Actual all-order coefficient heat drift before expanding the
mean-gradient product into cumulant subset contractions. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

 theorem directionalWordDerivative_append (f : Space n → ℝ) (vs ws : List (Space n)) :
    directionalWordDerivative f (vs++ws) =
      directionalWordDerivative (directionalWordDerivative f ws) vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.cons_append]
    change (fun z => fderiv ℝ (directionalWordDerivative f (vs++ws)) z v) =
      (fun z => fderiv ℝ (directionalWordDerivative (directionalWordDerivative f ws) vs) z v)
    rw [ih]

 theorem contDiffOn_coordinateHessian_local
    {f : Space n → ℝ} {r : ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (ball 0 r)) (i j : Fin n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => coordinateHessian f z i j) (ball 0 r) := by
  exact contDiffOn_word_of_isOpen isOpen_ball hf
    [EuclideanSpace.single i 1,EuclideanSpace.single j 1]

 theorem contDiffOn_coordinateLaplacian_local
    {f : Space n → ℝ} {r : ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (ball 0 r)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (coordinateLaplacian f) (ball 0 r) := by
  apply ContDiffOn.sum
  intro i hi
  exact contDiffOn_coordinateHessian_local hf i i

 theorem iteratedFDeriv_coordinateHessian_local
    {f : Space n → ℝ} {r : ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (ball 0 r)) (hr : 0 < r)
    (d : ℕ) (m : Fin d → Space n) (i j : Fin n) :
    iteratedFDeriv ℝ d (fun z => coordinateHessian f z i j) 0 m =
      iteratedFDeriv ℝ (d+2) f 0
        (Fin.cons (EuclideanSpace.single i 1) (Fin.cons (EuclideanSpace.single j 1) m)) := by
  have h0 : (0 : Space n) ∈ ball 0 r := by simpa using hr
  let w : List (Space n) := [EuclideanSpace.single i 1,EuclideanSpace.single j 1]
  calc
    _ = directionalWordDerivative (fun z => coordinateHessian f z i j) (List.ofFn m) 0 :=
      (local_word_ofFn isOpen_ball (contDiffOn_coordinateHessian_local hf i j) m h0).symm
    _ = directionalWordDerivative f (List.ofFn m++w) 0 := by
      rw [directionalWordDerivative_append]
      rfl
    _ = directionalWordDerivative f (w++List.ofFn m) 0 :=
      local_word_perm isOpen_ball hf (List.perm_append_comm) h0
    _ = _ := by
      simpa only [w,List.ofFn_cons,List.cons_append,List.nil_append] using
        local_word_ofFn isOpen_ball hf
          (Fin.cons (EuclideanSpace.single i 1) (Fin.cons (EuclideanSpace.single j 1) m)) h0

 theorem iteratedFDeriv_coordinateLaplacian_local
    {f : Space n → ℝ} {r : ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (ball 0 r)) (hr : 0 < r)
    (d : ℕ) (m : Fin d → Space n) :
    iteratedFDeriv ℝ d (coordinateLaplacian f) 0 m =
      ∑ i : Fin n, iteratedFDeriv ℝ (d+2) f 0
        (Fin.cons (EuclideanSpace.single i 1) (Fin.cons (EuclideanSpace.single i 1) m)) := by
  have h0 : (0 : Space n) ∈ ball 0 r := by simpa using hr
  unfold coordinateLaplacian
  rw [iteratedFDeriv_fun_sum_apply (fun i hi =>
    ((contDiffOn_coordinateHessian_local hf i i).contDiffAt
      (isOpen_ball.mem_nhds h0)).of_le (by simp)),sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact iteratedFDeriv_coordinateHessian_local hf hr d m i i

 def actualAppellHeatCoefficientGenerator (μ : Measure (Space n)) (f : Space n → ℝ)
    (d : ℕ) (m : Fin d → Space n) : ℝ :=
  derivWithin (fun s : ℝ => actualDampedMixedJet μ f d s m) (Ici 0) 0+
    (1/2 : ℝ)*(∑ i : Fin n, iteratedFDeriv ℝ (d+2) (actualDampedAverage μ f 0) 0
      (Fin.cons (EuclideanSpace.single i 1) (Fin.cons (EuclideanSpace.single i 1) m)))

/-- Genuine all-order coefficient drift.  The right side is the actual
theta derivative of the actual tilted mean times actual expectation
gradient.  Its subsequent subset expansion gives manuscript (3.7). -/
 theorem actualAppellHeatCoefficientGenerator_eq_mean_gradient_jet
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (d : ℕ) (m : Fin d → Space n) :
    actualAppellHeatCoefficientGenerator μ f d m =
      -iteratedFDeriv ℝ d
        (fun z => ∑ i : Fin n, actualTiltMeanCoordinate μ i z*
          coordinateDerivative (actualDampedAverage μ f 0) i z) 0 m := by
  obtain ⟨r,hr,hD,h1D⟩ := exists_common_local_exponential_domains hLC hf
  let A := actualDampedAverage μ f 0
  let R := actualDampingResponse μ f
  let H : Space n → ℝ := fun z => ∑ i : Fin n, actualTiltMeanCoordinate μ i z*
    coordinateDerivative A i z
  have hA : ContDiffOn ℝ (⊤ : ℕ∞) A (ball 0 r) :=
    contDiffOn_actualDampedAverage hD h1D (show (0 : ℝ) ≤ 0 from le_rfl)
  have hR : ContDiffOn ℝ (⊤ : ℕ∞) R (ball 0 r) := contDiffOn_actualDampingResponse hD h1D
  have hL : ContDiffOn ℝ (⊤ : ℕ∞) (coordinateLaplacian A) (ball 0 r) :=
    contDiffOn_coordinateLaplacian_local hA
  have h0 : (0 : Space n) ∈ ball 0 r := by simpa using hr
  have he : (fun z => R z+(1/2 : ℝ)*coordinateLaplacian A z) =ᶠ[𝓝 0] -H := by
    filter_upwards [isOpen_ball.mem_nhds h0] with z hz
    exact actualDampingResponse_add_half_laplacian hD h1D
      (by simpa only [mem_ball,dist_zero_right] using hz)
  have hd := congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin d => Space n) ℝ => T m)
    ((he.iteratedFDeriv (𝕜 := ℝ) d).eq_of_nhds)
  have hRa : ContDiffAt ℝ d R 0 := (hR.contDiffAt (isOpen_ball.mem_nhds h0)).of_le (by simp)
  have hLa : ContDiffAt ℝ d (coordinateLaplacian A) 0 :=
    (hL.contDiffAt (isOpen_ball.mem_nhds h0)).of_le (by simp)
  change iteratedFDeriv ℝ d (R+(1/2 : ℝ) • coordinateLaplacian A) 0 m =
    iteratedFDeriv ℝ d (-H) 0 m at hd
  have hScale : ContDiffAt ℝ d ((1/2 : ℝ) • coordinateLaplacian A) 0 := by
    simpa only [Pi.smul_def] using hLa.const_smul (1/2 : ℝ)
  rw [iteratedFDeriv_add_apply hRa hScale,
    iteratedFDeriv_const_smul_apply hLa,iteratedFDeriv_neg_apply] at hd
  simp only [ContinuousMultilinearMap.add_apply,ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.neg_apply,smul_eq_mul] at hd
  unfold actualAppellHeatCoefficientGenerator
  rw [(hasDerivWithinAt_actualDampedMixedJet_response hLC hf d m).derivWithin
    (uniqueDiffWithinAt_Ici 0),← iteratedFDeriv_coordinateLaplacian_local hA hr d m]
  exact hd

 theorem actualAppellHeatCoefficientGenerator_eq_labeled_masks
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (d : ℕ) (m : Fin d → Space n) :
    actualAppellHeatCoefficientGenerator μ f d m =
      -(∑ i : Fin n, ∑ s : Fin d → Bool,
        directionalWordDerivative (actualTiltMeanCoordinate μ i) (maskedDirections m s) 0*
          directionalWordDerivative (actualDampedAverage μ f 0)
            (maskedDirections m (fun j => !(s j))++[EuclideanSpace.single i 1]) 0) := by
  obtain ⟨r,hr,hD,h1D⟩ := exists_common_local_exponential_domains hLC hf
  let A := actualDampedAverage μ f 0
  have hA := contDiffOn_actualDampedAverage hD h1D (show (0 : ℝ) ≤ 0 from le_rfl)
  have h0 : (0 : Space n) ∈ ball 0 r := by simpa using hr
  have hm (i : Fin n) : ContDiffOn ℝ (⊤ : ℕ∞) (actualTiltMeanCoordinate μ i) (ball 0 r) := by
    have hi : LocalNormExponentialDomain μ (fun x : Space n => x i) r := by
      simpa only [one_mul] using h1D.mul_coordinate i
    exact contDiffOn_actualDampedAverage hi h1D (show (0 : ℝ) ≤ 0 from le_rfl)
  have hg (i : Fin n) : ContDiffOn ℝ (⊤ : ℕ∞) (coordinateDerivative A i) (ball 0 r) :=
    contDiffOn_word_of_isOpen isOpen_ball hA [EuclideanSpace.single i 1]
  rw [actualAppellHeatCoefficientGenerator_eq_mean_gradient_jet hLC hf d m]
  congr 1
  rw [iteratedFDeriv_fun_sum_apply (fun i hi =>
    (((hm i).mul (hg i)).contDiffAt (isOpen_ball.mem_nhds h0)).of_le (by simp)),sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have hw := local_word_ofFn isOpen_ball ((hm i).mul (hg i)) m h0
  change directionalWordDerivative (fun z => actualTiltMeanCoordinate μ i z*coordinateDerivative A i z)
    (List.ofFn m) 0 = iteratedFDeriv ℝ d
      (fun z => actualTiltMeanCoordinate μ i z*coordinateDerivative A i z) 0 m at hw
  rw [← hw,local_word_product_masks isOpen_ball (hm i) (hg i) m h0]
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  rw [directionalWordDerivative_append]
  rfl

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualAppellHeatCoefficientGenerator_eq_mean_gradient_jet
#print axioms KLS.DeterministicBridgeIntegration.actualAppellHeatCoefficientGenerator_eq_labeled_masks

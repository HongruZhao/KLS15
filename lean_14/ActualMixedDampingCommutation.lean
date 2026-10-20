import PointwiseMultilinearDerivative
import Mathlib

/-! Genuine all-order mixed normalized tilt/right-damping commutation.
Pointwise mixed derivatives form a symmetric continuous multilinear
tensor.  The proved directional identity determines it uniquely. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

 theorem actualDampedNumerator_one_pos
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] {r : ℝ}
    (h1 : LocalNormExponentialDomain μ (fun _ => 1) r)
    {s : ℝ} (hs : 0 ≤ s) {z : Space n} (hz : ‖z‖ ≤ r) :
    0 < actualDampedNumerator μ (fun _ => 1) s z := by
  have hi := (LocalNormExponentialDomain.mul_nonneg_damping h1 hs).integrable_tilt hz
  have hie : Integrable (fun x : Space n => Real.exp (inner ℝ z x-s*(‖x‖^2/2))) μ := by
    convert hi using 1
    funext x
    simp only [one_mul,sub_eq_add_neg,Real.exp_add]
    ring
  convert integral_exp_pos hie using 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [actualDampedNumerator,one_mul,sub_eq_add_neg,Real.exp_add]
    ring

 theorem contDiffOn_actualDampedAverage
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r)
    (h1 : LocalNormExponentialDomain μ (fun _ => 1) r)
    {s : ℝ} (hs : 0 ≤ s) :
    ContDiffOn ℝ (⊤ : ℕ∞) (actualDampedAverage μ f s) (ball 0 r) := by
  have hsN (g : Space n → ℝ) (hg : LocalNormExponentialDomain μ g r) :
      ContDiffOn ℝ (⊤ : ℕ∞) (actualDampedNumerator μ g s) (ball 0 r) := by
    convert contDiffOn_tiltNumerator_of_localNormExponentialDomain
      (LocalNormExponentialDomain.mul_nonneg_damping hg hs) using 1
    funext z
    simp only [actualDampedNumerator,tiltNumerator,zero_add]
  exact (hsN f hf).div (hsN (fun _ => 1) h1) (fun z hz =>
    (actualDampedNumerator_one_pos h1 hs
      (show ‖z‖ ≤ r from (by simpa only [mem_ball,dist_zero_right] using hz : ‖z‖ < r).le)).ne')

 theorem contDiffOn_actualDampingResponse
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r)
    (h1 : LocalNormExponentialDomain μ (fun _ => 1) r) :
    ContDiffOn ℝ (⊤ : ℕ∞) (actualDampingResponse μ f) (ball 0 r) := by
  have hrD : LocalNormExponentialDomain μ (fun x : Space n => ‖x‖^2/2) r := by
    simpa only [one_mul] using LocalNormExponentialDomain.mul_quadratic_rate h1
  exact (contDiffOn_actualDampedAverage (LocalNormExponentialDomain.mul_quadratic_rate hf)
      h1 (show (0 : ℝ) ≤ 0 from le_rfl)).neg.add
    ((contDiffOn_actualDampedAverage hf h1 (show (0 : ℝ) ≤ 0 from le_rfl)).mul
      (contDiffOn_actualDampedAverage hrD h1 (show (0 : ℝ) ≤ 0 from le_rfl)))

 theorem actualDampedDirectionalJet_eq_mixed
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r)
    (h1 : LocalNormExponentialDomain μ (fun _ => 1) r) (hr : 0 < r)
    {s : ℝ} (hs : 0 ≤ s) (d : ℕ) (v : Space n) :
    actualDampedDirectionalJet μ f d v s = actualDampedMixedJet μ f d s (fun _ => v) := by
  let L : ℝ →L[ℝ] Space n := ContinuousLinearMap.toSpanSingleton ℝ v
  have hN : ContDiffAt ℝ d (actualDampedAverage μ f s) 0 :=
    (contDiffAt_actualDampedAverage_zero hf h1 hr hs).of_le (by simp)
  have he := iteratedFDeriv_comp_clm_of_contDiffAt L 0
    (show ContDiffAt ℝ d (actualDampedAverage μ f s) (L 0) by simpa using hN)
  unfold actualDampedDirectionalJet actualDampedMixedJet
  change iteratedFDeriv ℝ d ((actualDampedAverage μ f s) ∘ L) 0 (fun _ => (1 : ℝ)) = _
  rw [he]
  simp [L,ContinuousMultilinearMap.compContinuousLinearMap_apply]

 theorem actualDirectionalDampingResponseJet_eq_mixed
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r)
    (h1 : LocalNormExponentialDomain μ (fun _ => 1) r) (hr : 0 < r)
    (d : ℕ) (v : Space n) :
    actualDirectionalDampingResponseJet μ f d v =
      iteratedFDeriv ℝ d (actualDampingResponse μ f) 0 (fun _ => v) := by
  let L : ℝ →L[ℝ] Space n := ContinuousLinearMap.toSpanSingleton ℝ v
  have hN : ContDiffAt ℝ d (actualDampingResponse μ f) 0 :=
    (contDiffAt_actualDampingResponse_zero hf h1 hr).of_le (by simp)
  have he := iteratedFDeriv_comp_clm_of_contDiffAt L 0
    (show ContDiffAt ℝ d (actualDampingResponse μ f) (L 0) by simpa using hN)
  unfold actualDirectionalDampingResponseJet
  change iteratedFDeriv ℝ d ((actualDampingResponse μ f) ∘ L) 0 (fun _ => (1 : ℝ)) = _
  rw [he]
  simp [L,ContinuousMultilinearMap.compContinuousLinearMap_apply]

/-- This is a genuine family derivative for every mixed Appell tensor
entry.  There is no regularity, commutation, or evolution premise. -/
 theorem hasDerivWithinAt_actualDampedMixedJet_response
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (d : ℕ) (m : Fin d → Space n) :
    HasDerivWithinAt (fun s : ℝ => actualDampedMixedJet μ f d s m)
      (iteratedFDeriv ℝ d (actualDampingResponse μ f) 0 m) (Ici 0) 0 := by
  obtain ⟨r,hr,hD,h1D⟩ := exists_common_local_exponential_domains hLC hf
  let T : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin d => Space n) ℝ :=
    fun s => iteratedFDeriv ℝ d (actualDampedAverage μ f s) 0
  have hT (m : Fin d → Space n) :
      DifferentiableWithinAt ℝ (fun s : ℝ => T s m) (Ici 0) 0 :=
    differentiableWithinAt_actualDampedMixedJet hLC hf d m
  have hTsym (s : ℝ) (hs : 0 ≤ s) : MultilinearPermutationInvariant (T s) := by
    intro v σ
    exact local_iteratedFDeriv_comp_perm isOpen_ball
      (contDiffOn_actualDampedAverage hD h1D hs) v σ
      (by simpa using hr : (0 : Space n) ∈ ball 0 r)
  let D := pointwiseRightDerivativeTensor T hT
  let R := iteratedFDeriv ℝ d (actualDampingResponse μ f) 0
  have hDsym : MultilinearPermutationInvariant D :=
    pointwiseRightDerivativeTensor_symmetric T hT hTsym
  have hRsym : MultilinearPermutationInvariant R := by
    intro v σ
    exact local_iteratedFDeriv_comp_perm isOpen_ball
      (contDiffOn_actualDampingResponse hD h1D) v σ
      (by simpa using hr : (0 : Space n) ∈ ball 0 r)
  have heq : D = R := by
    apply symmetric_multilinear_eq_of_diagonal D R hDsym hRsym
    intro v
    change derivWithin (fun s : ℝ => actualDampedMixedJet μ f d s (fun _ => v)) (Ici 0) 0 = _
    have he : derivWithin (fun s : ℝ => actualDampedMixedJet μ f d s (fun _ => v)) (Ici 0) 0 =
        derivWithin (fun s : ℝ => actualDampedDirectionalJet μ f d v s) (Ici 0) 0 := by
      apply derivWithin_congr
      · intro s hs
        exact (actualDampedDirectionalJet_eq_mixed hD h1D hr hs d v).symm
      · exact (actualDampedDirectionalJet_eq_mixed hD h1D hr (show (0 : ℝ) ≤ 0 from le_rfl) d v).symm
    rw [he,derivWithin_actualDampedDirectionalJet_eq_response hLC hf d v,
      actualDirectionalDampingResponseJet_eq_mixed hD h1D hr d v]
  have hm := congrArg (fun S : ContinuousMultilinearMap ℝ (fun _ : Fin d => Space n) ℝ => S m) heq
  change derivWithin (fun s : ℝ => actualDampedMixedJet μ f d s m) (Ici 0) 0 =
    iteratedFDeriv ℝ d (actualDampingResponse μ f) 0 m at hm
  rw [← hm]
  exact (differentiableWithinAt_actualDampedMixedJet hLC hf d m).hasDerivWithinAt

 theorem exponentialTilt_actualDampedTiltLaw
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 ≤ s) (z : Space n) :
    exponentialTilt (actualDampedTiltLaw μ 0 s) z = actualDampedTiltLaw μ z s := by
  have hi : Integrable (fun x : Space n => Real.exp (-s*(‖x‖^2/2))) μ := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    exact Eventually.of_forall fun x => by
      simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖x‖])
  change (μ.tilted (fun x => inner ℝ (0 : Space n) x-s*(‖x‖^2/2))).tilted
    (fun x => inner ℝ z x) = μ.tilted (fun x => inner ℝ z x-s*(‖x‖^2/2))
  rw [tilted_tilted (by simpa only [inner_zero_left,zero_sub,neg_mul] using hi)]
  congr 1
  funext x
  simp only [Pi.add_apply,inner_zero_left]
  ring

 theorem actualAppellCoefficient_dampedLaw_eq_mixed
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 ≤ s) (f : Space n → ℝ) (d : ℕ) (a : Fin d → Fin n) :
    actualAppellCoefficient (actualDampedTiltLaw μ 0 s) f d a =
      actualDampedMixedJet μ f d s (fun j => EuclideanSpace.single (a j) 1) := by
  unfold actualAppellCoefficient actualDampedMixedJet
  simp_rw [exponentialTilt_actualDampedTiltLaw hs,← actualDampedAverage_eq_integral]

/-- The literal coefficient of the literal varying probability law has
the proved derivative; this is not only a numerator-jet statement. -/
 theorem hasDerivWithinAt_actualAppellCoefficient_dampedLaw
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (d : ℕ) (a : Fin d → Fin n) :
    HasDerivWithinAt
      (fun s : ℝ => actualAppellCoefficient (actualDampedTiltLaw μ 0 s) f d a)
      (iteratedFDeriv ℝ d (actualDampingResponse μ f) 0
        (fun j => EuclideanSpace.single (a j) 1)) (Ici 0) 0 := by
  apply (hasDerivWithinAt_actualDampedMixedJet_response hLC hf d
    (fun j => EuclideanSpace.single (a j) 1)).congr_of_mem
  · intro s hs
    exact actualAppellCoefficient_dampedLaw_eq_mixed hs f d a
  · simp

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.hasDerivWithinAt_actualDampedMixedJet_response
#print axioms KLS.DeterministicBridgeIntegration.hasDerivWithinAt_actualAppellCoefficient_dampedLaw

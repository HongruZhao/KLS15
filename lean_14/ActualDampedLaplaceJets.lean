import ActualDampingDerivative
import ActualAppellTiltJets
import KLS.LocalTiltNumeratorMoments
import KLS.LocalMixedFrechet
import Mathlib

/-! Arbitrary-order genuine Laplace-jet/right-damping commutation.
The numerator jets are actual iterated Frechet derivatives of the actual
damped integral, and every claimed parameter derivative is proved. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 3

 def actualDampedNumerator (μ : Measure (Space n)) (f : Space n → ℝ)
    (s : ℝ) (z : Space n) : ℝ :=
  ∫ x, f x*Real.exp (-s*(‖x‖^2/2))*Real.exp (inner ℝ z x) ∂μ

 def actualDampedTiltLaw (μ : Measure (Space n)) (z : Space n) (s : ℝ) : Measure (Space n) :=
  μ.tilted (fun x => inner ℝ z x-s*(‖x‖^2/2))

 def actualDampedAverage (μ : Measure (Space n)) (f : Space n → ℝ)
    (s : ℝ) (z : Space n) : ℝ :=
  actualDampedNumerator μ f s z/actualDampedNumerator μ (fun _ => 1) s z

 theorem actualDampedAverage_eq_integral (μ : Measure (Space n)) (f : Space n → ℝ)
    (s : ℝ) (z : Space n) :
    actualDampedAverage μ f s z = ∫ x, f x ∂actualDampedTiltLaw μ z s := by
  change _ = tiltAverage μ (fun x => inner ℝ z x-s*(‖x‖^2/2)) f
  rw [tiltAverage_eq_ratio]
  unfold actualDampedAverage actualDampedNumerator tiltPartition
  simp_rw [sub_eq_add_neg,Real.exp_add]
  congr 1
  · apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  · apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring

 def actualDampedDirectionalJet (μ : Measure (Space n)) (f : Space n → ℝ)
    (d : ℕ) (v : Space n) (s : ℝ) : ℝ :=
  iteratedDeriv d (fun t : ℝ => actualDampedAverage μ f s (t • v)) 0

 def actualDampedDirectionalRawJet (μ : Measure (Space n)) (f : Space n → ℝ)
    (d : ℕ) (v : Space n) (s : ℝ) : ℝ :=
  iteratedDeriv d (fun t : ℝ => actualDampedNumerator μ f s (t • v)) 0

 theorem LocalNormExponentialDomain.mul_nonneg_damping
    {μ : Measure (Space n)} {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r) {s : ℝ} (hs : 0 ≤ s) :
    LocalNormExponentialDomain μ (fun x => f x*Real.exp (-s*(‖x‖^2/2))) r := by
  refine ⟨hf.1.mul (by fun_prop),fun m => ?_⟩
  apply (hf.2 m).mono' (by exact ((hf.1.mul (by fun_prop)).norm.mul (by fun_prop)).mul (by fun_prop))
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),norm_mul]
    simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-s*(‖x‖^2/2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖x‖])
    calc
      _ ≤ |f x| * 1*‖x‖^m*Real.exp (r*‖x‖) := by gcongr
      _ = _ := by ring

 theorem LocalNormExponentialDomain.integrable_quadratic_rate
    {μ : Measure (Space n)} {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r) (hr : 0 < r) :
    Integrable (fun x => ‖f x‖*(‖x‖^2/2)) μ := by
  apply (hf.2 2).mono' ((hf.1.norm).mul (by fun_prop))
  exact Eventually.of_forall fun x => by
    change |‖f x‖*(‖x‖^2/2)| ≤ ‖f x‖*‖x‖^2*Real.exp (r*‖x‖)
    rw [abs_of_nonneg (by positivity)]
    have he : 1 ≤ Real.exp (r*‖x‖) := Real.one_le_exp_iff.mpr (by positivity)
    nlinarith [mul_nonneg (norm_nonneg (f x)) (sq_nonneg ‖x‖)]

 theorem iteratedFDeriv_actualDampedNumerator_zero
    {μ : Measure (Space n)} {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r) (hr : 0 < r)
    {s : ℝ} (hs : 0 ≤ s) (d : ℕ) (m : Fin d → Space n) :
    iteratedFDeriv ℝ d (actualDampedNumerator μ f s) 0 m =
      ∫ x, (f x*(∏ j, inner ℝ x (m j)))*Real.exp (-s*(‖x‖^2/2)) ∂μ := by
  have he : actualDampedNumerator μ f s =
      tiltNumerator μ (fun _ => 0) (fun x => f x*Real.exp (-s*(‖x‖^2/2))) := by
    funext z
    simp only [actualDampedNumerator,tiltNumerator,zero_add]
  rw [he,iteratedFDeriv_tiltNumerator_moment_of_local
    (LocalNormExponentialDomain.mul_nonneg_damping hf hs) (by simpa using hr : ‖(0 : Space n)‖ < r)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [inner_zero_left,Real.exp_zero,mul_one]
    ring

/-- Arbitrary tensor order: differentiate the actual theta jet in the
nonnegative damping parameter. This proves commutation for the Laplace
numerator directly, with all polynomial domination derived locally. -/
 theorem hasDerivWithinAt_damped_laplace_jet
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (d : ℕ) (m : Fin d → Space n) :
    HasDerivWithinAt
      (fun s : ℝ => iteratedFDeriv ℝ d (actualDampedNumerator μ f s) 0 m)
      (-∫ x, (f x*(∏ j, inner ℝ x (m j)))*(‖x‖^2/2) ∂μ) (Ici 0) 0 := by
  obtain ⟨r,hr,hD,hD1⟩ := exists_common_local_exponential_domains hLC hf
  let g : Space n → ℝ := fun x => f x*∏ j, inner ℝ x (m j)
  have hg : LocalNormExponentialDomain μ g r := by
    convert hD.mul_innerWord (List.ofFn m) using 1
    funext x
    simp only [g,innerWordMonomial,List.map_ofFn,List.prod_ofFn,Function.comp_apply]
  have hgi : Integrable g μ := by
    simpa only [inner_zero_left,Real.exp_zero,mul_one] using
      hg.integrable_tilt (show ‖(0 : Space n)‖ ≤ r by simpa using hr.le)
  have hd := hasDerivWithinAt_damping_numerator hgi
    (show AEStronglyMeasurable (fun x : Space n => ‖x‖^2/2) μ by fun_prop)
    (fun _ => by positivity) (LocalNormExponentialDomain.integrable_quadratic_rate hg hr)
  apply hd.congr_of_mem
  · intro s hs
    exact iteratedFDeriv_actualDampedNumerator_zero hD hr hs d m
  · simp

 theorem actualDampedDirectionalRawJet_eq_mixed
    {μ : Measure (Space n)} {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r) (hr : 0 < r)
    {s : ℝ} (hs : 0 ≤ s) (d : ℕ) (v : Space n) :
    actualDampedDirectionalRawJet μ f d v s =
      iteratedFDeriv ℝ d (actualDampedNumerator μ f s) 0 (fun _ => v) := by
  let L : ℝ →L[ℝ] Space n := ContinuousLinearMap.toSpanSingleton ℝ v
  have heN : actualDampedNumerator μ f s =
      tiltNumerator μ (fun _ => 0) (fun x => f x*Real.exp (-s*(‖x‖^2/2))) := by
    funext z
    simp only [actualDampedNumerator,tiltNumerator,zero_add]
  have hN : ContDiffAt ℝ d (actualDampedNumerator μ f s) 0 := by
    rw [heN]
    exact ((contDiffOn_tiltNumerator_of_localNormExponentialDomain
      (LocalNormExponentialDomain.mul_nonneg_damping hf hs)).contDiffAt
      (isOpen_ball.mem_nhds (by simpa using hr : (0 : Space n) ∈ ball 0 r))).of_le (by simp)
  have he := iteratedFDeriv_comp_clm_of_contDiffAt L 0
    (show ContDiffAt ℝ d (actualDampedNumerator μ f s) (L 0) by simpa using hN)
  unfold actualDampedDirectionalRawJet
  change iteratedFDeriv ℝ d ((actualDampedNumerator μ f s) ∘ L) 0 (fun _ => (1 : ℝ)) = _
  rw [he]
  simp [L,ContinuousMultilinearMap.compContinuousLinearMap_apply]

 theorem actualDampedDirectionalRawJet_eq_moment
    {μ : Measure (Space n)} {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r) (hr : 0 < r)
    {s : ℝ} (hs : 0 ≤ s) (d : ℕ) (v : Space n) :
    actualDampedDirectionalRawJet μ f d v s =
      ∫ x, (f x*(inner ℝ x v)^d)*Real.exp (-s*(‖x‖^2/2)) ∂μ := by
  rw [actualDampedDirectionalRawJet_eq_mixed hf hr hs,
    iteratedFDeriv_actualDampedNumerator_zero hf hr hs]
  simp

 theorem hasDerivWithinAt_damped_directional_raw_jet
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (d : ℕ) (v : Space n) :
    HasDerivWithinAt (fun s : ℝ => actualDampedDirectionalRawJet μ f d v s)
      (-∫ x, (f x*(inner ℝ x v)^d)*(‖x‖^2/2) ∂μ) (Ici 0) 0 := by
  obtain ⟨r,hr,hD,hD1⟩ := exists_common_local_exponential_domains hLC hf
  have hd := hasDerivWithinAt_damped_laplace_jet hLC hf d (fun _ => v)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hd
  apply hd.congr_of_mem
  · intro s hs
    exact actualDampedDirectionalRawJet_eq_mixed hD hr hs d v
  · simp

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.hasDerivWithinAt_damped_laplace_jet

#print axioms KLS.DeterministicBridgeIntegration.hasDerivWithinAt_damped_directional_raw_jet

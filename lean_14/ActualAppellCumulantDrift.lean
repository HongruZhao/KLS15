import ActualAppellHeatDrift
import ActualLocalCumulant
import KLS.MaskedDirections
import KLS.AdaptiveCumulantNoiseWords

/-! Literal cumulant contraction form of the genuine all-order Appell drift.
The empty and singleton subsets are evaluated using actual isotropy. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem sum_finsets_empty_singletons_remainder {d : ℕ}
    (g : Finset (Fin d) → ℝ) :
    (∑ S : Finset (Fin d), g S) = g ∅+(∑ j : Fin d, g {j})+
      ∑ S : Finset (Fin d), if 2 ≤ S.card then g S else 0 := by
  classical
  have he (S : Finset (Fin d)) : g S =
      (if S=∅ then g ∅ else 0)+(if S.card=1 then g S else 0)+
        (if 2 ≤ S.card then g S else 0) := by
    by_cases h0 : S=∅
    · simp [h0]
    · have hp : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0)
      by_cases h1 : S.card=1
      · simp [h0,h1]
      · have h2 : 2 ≤ S.card := by omega
        simp [h0,h1,h2]
  conv_lhs => arg 2; ext S; rw [he S]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  congr 1
  rw [← Finset.sum_filter]
  have hsets : Finset.univ.filter (fun S : Finset (Fin d) => S.card=1) =
      Finset.univ.image (fun j : Fin d => ({j} : Finset (Fin d))) := by
    ext S
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
    simpa only [eq_comm] using (Finset.card_eq_one : S.card=1 ↔ ∃ a, S={a})
  rw [hsets,Finset.sum_image]
  intro i hi j hj hij
  exact Finset.singleton_injective hij

 theorem contDiffOn_logLaplace_of_local
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] {r : ℝ}
    (h1 : LocalNormExponentialDomain μ (fun _ => 1) r) :
    ContDiffOn ℝ (⊤ : ℕ∞) (tiltLogLaplace μ) (ball 0 r) := by
  intro z hz
  exact (contDiffAt_logLaplace_of_localNormExponentialDomain h1
    (by simpa only [mem_ball,dist_zero_right] using hz)).contDiffWithinAt

 theorem listCumulant_eq_local_word
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) (vs : List (Space n)) :
    listCumulant μ vs = directionalWordDerivative (tiltLogLaplace μ) vs 0 := by
  obtain ⟨r,hr,h1⟩ := hLC.exists_localNormExponentialDomain_one
  have hh := local_word_ofFn isOpen_ball (contDiffOn_logLaplace_of_local h1) vs.get
    (by simpa using hr : (0 : Space n) ∈ ball 0 r)
  simpa only [List.ofFn_get,listCumulant,cumulantTensor] using hh.symm

 theorem eventuallyEq_directionalWordDerivative {f g : Space n → ℝ}
    (he : f =ᶠ[𝓝 (0 : Space n)] g) (vs : List (Space n)) :
    directionalWordDerivative f vs =ᶠ[𝓝 (0 : Space n)] directionalWordDerivative g vs := by
  induction vs with
  | nil => exact he
  | cons v vs ih =>
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with z hz
    exact congrArg (fun L : Space n →L[ℝ] ℝ => L v) hz

 theorem directionalWordDerivative_eventuallyEq {f g : Space n → ℝ}
    (he : f =ᶠ[𝓝 (0 : Space n)] g) (vs : List (Space n)) :
    directionalWordDerivative f vs 0 = directionalWordDerivative g vs 0 :=
  (eventuallyEq_directionalWordDerivative he vs).eq_of_nhds

 theorem actualDampedAverage_zero_eq_tilt_average (μ : Measure (Space n))
    (f : Space n → ℝ) : actualDampedAverage μ f 0 =
      fun z => ∫ x, f x ∂exponentialTilt μ z := by
  funext z
  rw [actualDampedAverage_eq_integral]
  congr 1
  unfold actualDampedTiltLaw exponentialTilt
  congr 1
  funext x
  simp

 theorem actualTiltMean_word_eq_cumulant
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) (i : Fin n) (vs : List (Space n)) :
    directionalWordDerivative (actualTiltMeanCoordinate μ i) vs 0 =
      listCumulant μ (vs++[EuclideanSpace.single i 1]) := by
  obtain ⟨r,hr,h1⟩ := hLC.exists_localNormExponentialDomain_one
  have he : actualTiltMeanCoordinate μ i =ᶠ[𝓝 (0 : Space n)]
      directionalWordDerivative (tiltLogLaplace μ) [EuclideanSpace.single i 1] := by
    filter_upwards [ball_mem_nhds (0 : Space n) hr] with z hz
    unfold actualTiltMeanCoordinate
    rw [actualDampedAverage_zero_eq_tilt_average]
    have hh := fderiv_logLaplace_direction_eq_average_of_local h1
      (by simpa only [mem_ball,dist_zero_right] using hz) (EuclideanSpace.single i 1)
    simpa only [directionalWordDerivative_cons,directionalWordDerivative_nil,
      EuclideanSpace.inner_single_right,starRingEnd_apply,star_trivial,one_mul] using hh.symm
  rw [directionalWordDerivative_eventuallyEq he,
    ← directionalWordDerivative_append,← listCumulant_eq_local_word hLC]

 theorem euclidean_sum_coordinate_single (v : Space n) :
    (∑ i, v i • EuclideanSpace.single i 1) = v := by
  apply PiLp.ext
  intro i
  change (EuclideanSpace.proj i) (∑ j, v j • EuclideanSpace.single j 1) = v i
  rw [map_sum]
  simp

 theorem actualTiltMean_zero_of_isotropic
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hiso : IsIsotropic μ)
    (i : Fin n) : actualTiltMeanCoordinate μ i 0 = 0 := by
  unfold actualTiltMeanCoordinate
  rw [actualDampedAverage_zero_eq_tilt_average]
  simpa only [exponentialTilt_zero] using hiso.integral_coordinate i

 theorem actualTiltMean_singleton_of_isotropic
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    (hiso : IsIsotropic μ) (i : Fin n) (v : Space n) :
    directionalWordDerivative (actualTiltMeanCoordinate μ i) [v] 0 = v i := by
  unfold actualTiltMeanCoordinate
  rw [actualDampedAverage_zero_eq_tilt_average]
  change fderiv ℝ (fun z => ∫ x, x i ∂exponentialTilt μ z) 0 v = v i
  rw [(hasFDerivAt_normalized_tilt_average_zero_of_isotropic hLC hiso
    (hiso.memLp_coordinate i)).fderiv]
  simp [hiso.integral_coordinate_mul]

 theorem actualAppell_singleton_mask_contraction
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    (hiso : IsIsotropic μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    {d : ℕ} (m : Fin d → Space n) (j : Fin d) :
    (∑ i : Fin n,
      directionalWordDerivative (actualTiltMeanCoordinate μ i)
        (maskedDirections m (fun k => decide (k=j))) 0*
      directionalWordDerivative (actualDampedAverage μ f 0)
        (maskedDirections m (fun k => !(decide (k=j)))++[EuclideanSpace.single i 1]) 0) =
      iteratedFDeriv ℝ d (actualDampedAverage μ f 0) 0 m := by
  obtain ⟨r,hr,hD,h1D⟩ := exists_common_local_exponential_domains hLC hf
  have hA := contDiffOn_actualDampedAverage hD h1D (show (0 : ℝ) ≤ 0 from le_rfl)
  have h0 : (0 : Space n) ∈ ball 0 r := by simpa using hr
  let ws := maskedDirections m (fun k => !(decide (k=j)))
  let L := fderiv ℝ (directionalWordDerivative (actualDampedAverage μ f 0) ws) 0
  have he (i : Fin n) : directionalWordDerivative (actualDampedAverage μ f 0)
      (ws++[EuclideanSpace.single i 1]) 0 = L (EuclideanSpace.single i 1) :=
    local_word_perm isOpen_ball hA List.perm_append_comm h0
  simp_rw [maskedDirections_singleton,actualTiltMean_singleton_of_isotropic hLC hiso]
  change (∑ i : Fin n, (m j) i*directionalWordDerivative (actualDampedAverage μ f 0)
      (ws++[EuclideanSpace.single i 1]) 0) = _
  simp_rw [he,← smul_eq_mul,← map_smul,← map_sum,euclidean_sum_coordinate_single]
  change directionalWordDerivative (actualDampedAverage μ f 0) ([m j]++ws) 0 = _
  have hp := maskedDirections_append_complement m (fun k => decide (k=j))
  rw [maskedDirections_singleton] at hp
  exact (local_word_perm isOpen_ball hA hp h0).trans (local_word_ofFn isOpen_ball hA m h0)

 def actualAppellLowerDrift (μ : Measure (Space n)) (f : Space n → ℝ)
    (d : ℕ) (m : Fin d → Space n) : ℝ :=
  ∑ S : Finset (Fin d), if 2 ≤ S.card then
    ∑ i : Fin n,
      listCumulant μ (maskedDirections m (fun j => decide (j ∈ S))++[EuclideanSpace.single i 1])*
      directionalWordDerivative (actualDampedAverage μ f 0)
        (maskedDirections m (fun j => !(decide (j ∈ S)))++[EuclideanSpace.single i 1]) 0
    else 0

 /-- Literal full-class (3.7), with the manuscript's unnormalized B_d and
 the genuine subset/cumulant lower contraction (3.8). -/
 theorem actualAppellHeatCoefficientGenerator_eq_drift
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    (hiso : IsIsotropic μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (d : ℕ) (m : Fin d → Space n) :
    actualAppellHeatCoefficientGenerator μ f d m =
      -(d : ℝ)*iteratedFDeriv ℝ d (actualDampedAverage μ f 0) 0 m-
        actualAppellLowerDrift μ f d m := by
  classical
  let g : Finset (Fin d) → ℝ := fun S => ∑ i : Fin n,
    directionalWordDerivative (actualTiltMeanCoordinate μ i)
      (maskedDirections m (fun j => decide (j ∈ S))) 0*
    directionalWordDerivative (actualDampedAverage μ f 0)
      (maskedDirections m (fun j => !(decide (j ∈ S)))++[EuclideanSpace.single i 1]) 0
  have hg0 : g ∅ = 0 := by
    have he : (fun j : Fin d => decide (j ∈ (∅ : Finset (Fin d)))) = fun _ => false := by
      funext j
      simp
    simp only [g,he,maskedDirections_none,directionalWordDerivative_nil,
      actualTiltMean_zero_of_isotropic hiso,zero_mul,Finset.sum_const_zero]
  have hg1 (j : Fin d) : g {j} =
      iteratedFDeriv ℝ d (actualDampedAverage μ f 0) 0 m := by
    simp only [g,Finset.mem_singleton]
    exact actualAppell_singleton_mask_contraction hLC hiso hf m j
  have hgr : (∑ S : Finset (Fin d), if 2 ≤ S.card then g S else 0) =
      actualAppellLowerDrift μ f d m := by
    unfold actualAppellLowerDrift
    apply Finset.sum_congr rfl
    intro S hS
    split_ifs
    · exact Finset.sum_congr rfl fun i hi => by rw [actualTiltMean_word_eq_cumulant hLC]
    · rfl
  rw [actualAppellHeatCoefficientGenerator_eq_labeled_masks hLC hf d m,Finset.sum_comm]
  have hm : (∑ s : Fin d → Bool, ∑ i : Fin n,
      directionalWordDerivative (actualTiltMeanCoordinate μ i) (maskedDirections m s) 0*
        directionalWordDerivative (actualDampedAverage μ f 0)
          (maskedDirections m (fun j => !(s j))++[EuclideanSpace.single i 1]) 0) =
      ∑ S : Finset (Fin d), g S := by
    rw [← (maskFinsetEquiv d).sum_comp]
    apply Finset.sum_congr rfl
    intro s hs
    change _ = g (maskSet s)
    simp only [g,mem_maskSet,Bool.decide_coe]
  rw [hm,sum_finsets_empty_singletons_remainder g,hg0,hgr]
  simp_rw [hg1]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,zero_add]
  ring

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualTiltMean_word_eq_cumulant
#print axioms KLS.DeterministicBridgeIntegration.actualAppellHeatCoefficientGenerator_eq_drift

import ActualAppellCumulantDrift

/-! Genuine multiplication of an L² test by a coordinate in the Appell
calculus. All differentiation is local; the coordinate-multiplied test is
not assumed to lie in L². The lower term is an exact labelled cumulant sum. -/
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

 theorem actualDampedAverage_coordinate_mul_of_local
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] {f : Space n → ℝ} {r : ℝ}
    (hf : LocalNormExponentialDomain μ f r)
    (h1 : LocalNormExponentialDomain μ (fun _ => 1) r)
    {z : Space n} (hz : ‖z‖ < r) (i : Fin n) :
    actualDampedAverage μ (fun x => x i*f x) 0 z =
      coordinateDerivative (actualDampedAverage μ f 0) i z+
        actualTiltMeanCoordinate μ i z*actualDampedAverage μ f 0 z := by
  let N := tiltNumerator μ (fun _ => 0) f
  let Z := tiltNumerator μ (fun _ => 0) (fun _ => 1)
  let A := actualDampedAverage μ f 0
  have hNz := (contDiffOn_tiltNumerator_of_localNormExponentialDomain hf).contDiffAt
    (isOpen_ball.mem_nhds (by simpa using hz))
  have hZz := (contDiffOn_tiltNumerator_of_localNormExponentialDomain h1).contDiffAt
    (isOpen_ball.mem_nhds (by simpa using hz))
  have hAz := (contDiffOn_actualDampedAverage hf h1 (show (0 : ℝ) ≤ 0 from le_rfl)).contDiffAt
    (isOpen_ball.mem_nhds (by simpa using hz))
  have hzpos : 0 < Z z := by
    simpa only [Z,tiltNumerator,zero_add,one_mul] using
      integral_exp_pos (by simpa only [one_mul] using h1.integrable_tilt hz.le)
  have hAZ : (fun y => A y*Z y) =ᶠ[𝓝 z] N := by
    filter_upwards [hZz.continuousAt.eventually_ne hzpos.ne'] with y hy
    change actualDampedAverage μ f 0 y*Z y = N y
    simp only [actualDampedAverage,actualDampedNumerator,neg_zero,zero_mul,
      Real.exp_zero,mul_one,N,Z,tiltNumerator,zero_add]
    exact div_mul_cancel₀ _ (by simpa only [Z,tiltNumerator,zero_add] using hy)
  have hprod := coordinateDerivative_mul
    (hAz.differentiableAt (by simp)) (hZz.differentiableAt (by simp)) i
  have hpeq : coordinateDerivative (fun y => A y*Z y) i z = coordinateDerivative N i z :=
    congrArg (fun L : Space n →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hAZ.fderiv_eq
  rw [hpeq] at hprod
  have hmean : actualTiltMeanCoordinate μ i z = coordinateDerivative Z i z/Z z := by
    have hd := fderiv_tiltNumerator_apply_inner_of_local h1 hz (EuclideanSpace.single i 1)
    change actualDampedAverage μ (fun x => x i) 0 z =
      fderiv ℝ (tiltNumerator μ (fun _ => 0) (fun _ => 1)) z (EuclideanSpace.single i 1)/Z z
    rw [hd]
    simp [actualDampedAverage,actualDampedNumerator,tiltNumerator,Z,EuclideanSpace.inner_single_right]
  have htest : actualDampedAverage μ (fun x => x i*f x) 0 z = coordinateDerivative N i z/Z z := by
    have hd := fderiv_tiltNumerator_apply_inner_of_local hf hz (EuclideanSpace.single i 1)
    change actualDampedAverage μ (fun x => x i*f x) 0 z =
      fderiv ℝ (tiltNumerator μ (fun _ => 0) f) z (EuclideanSpace.single i 1)/Z z
    rw [hd]
    simp only [actualDampedAverage,actualDampedNumerator,neg_zero,zero_mul,
      Real.exp_zero,mul_one,tiltNumerator,Z,zero_add,
      EuclideanSpace.inner_single_right,RCLike.conj_to_real,one_mul]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  rw [htest,hmean]
  change coordinateDerivative N i z/Z z = coordinateDerivative A i z+
    coordinateDerivative Z i z/Z z*A z
  field_simp [hzpos.ne']
  nlinarith [hprod]

 def actualAppellCoordinateLower (μ : Measure (Space n)) (f : Space n → ℝ)
    {d : ℕ} (i : Fin n) (m : Fin d → Space n) : ℝ :=
  ∑ S : Finset (Fin d),
    listCumulant μ (maskedDirections m (fun j => decide (j ∈ S))++[EuclideanSpace.single i 1])*
      directionalWordDerivative (actualDampedAverage μ f 0)
        (maskedDirections m (fun j => !(decide (j ∈ S)))) 0

 theorem actualAppell_coordinate_mul_jet
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    {d : ℕ} (i : Fin n) (m : Fin d → Space n) :
    iteratedFDeriv ℝ d (actualDampedAverage μ (fun x => x i*f x) 0) 0 m =
      iteratedFDeriv ℝ (d+1) (actualDampedAverage μ f 0) 0
        (Fin.cons (EuclideanSpace.single i 1) m)+actualAppellCoordinateLower μ f i m := by
  classical
  obtain ⟨r,hr,hD,h1D⟩ := exists_common_local_exponential_domains hLC hf
  let A := actualDampedAverage μ f 0
  let M := actualTiltMeanCoordinate μ i
  have h0 : (0 : Space n) ∈ ball 0 r := by simpa using hr
  have hA := contDiffOn_actualDampedAverage hD h1D (show (0 : ℝ) ≤ 0 from le_rfl)
  have hMi : LocalNormExponentialDomain μ (fun x : Space n => x i) r := by
    simpa only [one_mul] using h1D.mul_coordinate i
  have hM := contDiffOn_actualDampedAverage hMi h1D (show (0 : ℝ) ≤ 0 from le_rfl)
  change ContDiffOn ℝ (⊤ : ℕ∞) M (ball 0 r) at hM
  change ContDiffOn ℝ (⊤ : ℕ∞) A (ball 0 r) at hA
  have hDA : ContDiffOn ℝ (⊤ : ℕ∞) (coordinateDerivative A i) (ball 0 r) :=
    contDiffOn_word_of_isOpen isOpen_ball hA [EuclideanSpace.single i 1]
  have he : actualDampedAverage μ (fun x => x i*f x) 0 =ᶠ[𝓝 (0 : Space n)]
      (fun z => coordinateDerivative A i z+M z*A z) := by
    filter_upwards [isOpen_ball.mem_nhds h0] with z hz
    exact actualDampedAverage_coordinate_mul_of_local hD h1D
      (by simpa only [mem_ball,dist_zero_right] using hz) i
  have hd := congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin d => Space n) ℝ => T m)
    ((he.iteratedFDeriv (𝕜 := ℝ) d).eq_of_nhds)
  have hDa : ContDiffAt ℝ d (coordinateDerivative A i) 0 :=
    (hDA.contDiffAt (isOpen_ball.mem_nhds h0)).of_le (by simp)
  have hPa : ContDiffAt ℝ d (fun z => M z*A z) 0 :=
    ((hM.mul hA).contDiffAt (isOpen_ball.mem_nhds h0)).of_le (by simp)
  change _ = iteratedFDeriv ℝ d ((coordinateDerivative A i)+(fun z => M z*A z)) 0 m at hd
  rw [iteratedFDeriv_add_apply hDa hPa] at hd
  simp only [ContinuousMultilinearMap.add_apply] at hd
  have hfirst : iteratedFDeriv ℝ d (coordinateDerivative A i) 0 m =
      iteratedFDeriv ℝ (d+1) A 0 (Fin.cons (EuclideanSpace.single i 1) m) := by
    have hw : directionalWordDerivative (coordinateDerivative A i) (List.ofFn m) 0 =
        iteratedFDeriv ℝ d (coordinateDerivative A i) 0 m :=
      local_word_ofFn isOpen_ball hDA m h0
    rw [← hw]
    change directionalWordDerivative (directionalWordDerivative A [EuclideanSpace.single i 1])
      (List.ofFn m) 0 = _
    rw [← directionalWordDerivative_append]
    rw [local_word_perm isOpen_ball hA List.perm_append_comm h0]
    simpa only [List.singleton_append,List.ofFn_cons] using
      local_word_ofFn isOpen_ball hA (Fin.cons (EuclideanSpace.single i 1) m) h0
  have hsecond : iteratedFDeriv ℝ d (fun z => M z*A z) 0 m =
      actualAppellCoordinateLower μ f i m := by
    have hw : directionalWordDerivative (fun z => M z*A z) (List.ofFn m) 0 =
        iteratedFDeriv ℝ d (fun z => M z*A z) 0 m :=
      local_word_ofFn isOpen_ball (hM.mul hA) m h0
    rw [← hw,local_word_product_masks isOpen_ball hM hA m h0]
    unfold actualAppellCoordinateLower
    rw [← (maskFinsetEquiv d).sum_comp]
    apply Finset.sum_congr rfl
    intro s hs
    change _ = listCumulant μ
      (maskedDirections m (fun j => decide (j ∈ maskSet s))++[EuclideanSpace.single i 1])*
        directionalWordDerivative (actualDampedAverage μ f 0)
          (maskedDirections m (fun j => !(decide (j ∈ maskSet s)))) 0
    simp only [mem_maskSet,Bool.decide_coe]
    exact congrArg (fun q : ℝ => q*directionalWordDerivative A
      (maskedDirections m (fun j => !(s j))) 0)
      (actualTiltMean_word_eq_cumulant hLC i (maskedDirections m s))
  exact hd.trans (by rw [hfirst,hsecond])

 theorem actualAppellCoefficient_coordinate_mul
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    {d : ℕ} (i : Fin n) (a : Fin d → Fin n) :
    actualAppellCoefficient μ (fun x => x i*f x) d a =
      actualAppellCoefficient μ f (d+1) (Fin.cons i a)+
        actualAppellCoordinateLower μ f i (fun j => EuclideanSpace.single (a j) 1) := by
  unfold actualAppellCoefficient
  rw [← actualDampedAverage_zero_eq_tilt_average,← actualDampedAverage_zero_eq_tilt_average]
  have he : (fun j : Fin (d+1) => (EuclideanSpace.single ((Fin.cons (α := fun _ => Fin n) i a) j) (1 : ℝ) : Space n)) =
      Fin.cons (α := fun _ => Space n) (EuclideanSpace.single i (1 : ℝ))
        (fun j => EuclideanSpace.single (a j) (1 : ℝ)) := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> simp
  rw [he]
  exact actualAppell_coordinate_mul_jet hLC hf i _

 theorem actualAppellCoefficient_zero_of_vanishing_words
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    {d k : ℕ} (hdk : d < k)
    (hzero : ∀ vs : List (Space n), vs.length < k →
      directionalWordDerivative (actualDampedAverage μ f 0) vs 0 = 0) :
    actualAppellCoefficient μ f d = 0 := by
  obtain ⟨r,hr,hD,h1D⟩ := exists_common_local_exponential_domains hLC hf
  have hA := contDiffOn_actualDampedAverage hD h1D (show (0 : ℝ) ≤ 0 from le_rfl)
  have h0 : (0 : Space n) ∈ ball 0 r := by simpa using hr
  funext a
  unfold actualAppellCoefficient
  rw [← actualDampedAverage_zero_eq_tilt_average]
  have hw : directionalWordDerivative (actualDampedAverage μ f 0)
      (List.ofFn (fun j => EuclideanSpace.single (a j) 1)) 0 =
      iteratedFDeriv ℝ d (actualDampedAverage μ f 0) 0
        (fun j => EuclideanSpace.single (a j) 1) :=
    local_word_ofFn isOpen_ball hA _ h0
  rw [← hw]
  exact hzero _ (by simpa only [List.length_ofFn] using hdk)

 theorem actualAppellCoordinateLower_zero_of_vanishing_words
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) (hiso : IsIsotropic μ)
    (f : Space n → ℝ) {d : ℕ} (i : Fin n) (m : Fin d → Space n)
    (hzero : ∀ vs : List (Space n), vs.length < d →
      directionalWordDerivative (actualDampedAverage μ f 0) vs 0 = 0) :
    actualAppellCoordinateLower μ f i m = 0 := by
  classical
  have hmean : listCumulant μ [EuclideanSpace.single i 1] = 0 := by
    have hh := actualTiltMean_word_eq_cumulant hLC i []
    simpa only [directionalWordDerivative_nil,List.nil_append,
      actualTiltMean_zero_of_isotropic hiso] using hh.symm
  unfold actualAppellCoordinateLower
  apply Finset.sum_eq_zero
  intro S hS
  by_cases he : S = ∅
  · subst S
    simp only [Finset.notMem_empty,decide_false,maskedDirections_none,
      List.nil_append,hmean,zero_mul]
  · have hset : maskSet (fun j => decide (j ∈ S)) = S := by ext j; simp
    have hcard : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
    have hc : S.card+Sᶜ.card=d := by simp
    have hlen : (maskedDirections m (fun j => !(decide (j ∈ S)))).length < d := by
      rw [maskedDirections_length,maskSet_complement,hset]
      omega
    rw [hzero _ hlen,mul_zero]

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualDampedAverage_coordinate_mul_of_local
#print axioms KLS.DeterministicBridgeIntegration.actualAppell_coordinate_mul_jet
#print axioms KLS.DeterministicBridgeIntegration.actualAppellCoefficient_coordinate_mul
#print axioms KLS.DeterministicBridgeIntegration.actualAppellCoefficient_zero_of_vanishing_words
#print axioms KLS.DeterministicBridgeIntegration.actualAppellCoordinateLower_zero_of_vanishing_words

import KLSConstantImprovement.ActualVectorDifferential405
import KLSConstantImprovement.ActualBoundedCoefficientL2Passage405

/-! A genuine C1 globally Lipschitz multivariate weak chain rule. One
simultaneous mollifier subsequence gives a.e. convergence of the whole
vector. Continuous bounded partial derivatives pass in L2 after each
compact test is inserted. No Lipschitz derivative premise is used. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff ENNReal NNReal
namespace KLSConstantImprovement.ActualGlobalWeakVectorChain405
open KLS ActualVectorL2Composition405 ActualVectorDifferential405
open ActualBoundedCoefficientL2Passage405 ActualWeightedL2PairingContinuity
variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem vector_chain_of_global_L2_weak
    {f : ι → Space n → ℝ} {i : Fin n}
    {F : ι → Lp ℝ 2 (volume : Measure (Space n))}
    (hf : ∀ j, MemLp (f j) 2 volume)
    (hF : ∀ j, HasWeakCoordinateDerivative (f j) i (F j))
    {η : (ι → ℝ) → ℝ} (hη : ContDiff ℝ 1 η) (hη0 : η 0 = 0)
    {L : ℝ≥0} (hLip : LipschitzWith L η) :
    HasLocalWeakCoordinateDerivative (fun x => η (fun j => f j x))
      (fun x => ∑ j, vectorPartial η j (fun a => f a x) * F j x) i := by
  intro ψ hψ hc
  let fm (k : ℕ) (j : ι) := mollify k (f j)
  let Fm (k : ℕ) (j : ι) := coordinateDerivative (mollify k (f j)) i
  have hfm (k : ℕ) (j : ι) : MemLp (fm k j) 2 volume := memLp_mollify (hf j) k
  have hFm (k : ℕ) (j : ι) : MemLp (Fm k j) 2 volume := by
    dsimp only [Fm]
    rw [(hF j).mollify_eq (hf j)]
    exact memLp_mollify (Lp.memLp (F j)) k
  have hfv (j : ι) : Tendsto (fun k => eLpNorm (fm k j - f j) 2 volume) atTop (𝓝 0) :=
    eLpNorm_mollify_sub_tendsto_zero (hf j)
  have hFd (j : ι) : Tendsto (fun k => eLpNorm (Fm k j - (F j : Space n → ℝ)) 2 volume)
      atTop (𝓝 0) := (hF j).eLpNorm_mollify_derivative_sub_tendsto_zero (hf j)
  obtain ⟨s, hs, hsae⟩ := exists_common_vector_subsequence hfm hf hfv
  let u (x : Space n) : ι → ℝ := fun j => f j x
  let um (k : ℕ) (x : Space n) : ι → ℝ := fun j => fm (s k) j x
  have hu : MemLp u 2 volume := MemLp.of_eval hf
  have hum (k : ℕ) : MemLp (um k) 2 volume := MemLp.of_eval (hfm (s k))
  have hulim : Tendsto (fun k => eLpNorm (um k - u) 2 volume) atTop (𝓝 0) :=
    (finite_vector_strong_L2 hfm hf hfv).comp hs.tendsto_atTop
  have hηm (k : ℕ) : MemLp (η ∘ um k) 2 volume := hLip.comp_memLp hη0 (hum k)
  have hηu : MemLp (η ∘ u) 2 volume := hLip.comp_memLp hη0 hu
  have hηlim : Tendsto (fun k => eLpNorm ((η ∘ um k) - (η ∘ u)) 2 volume) atTop (𝓝 0) :=
    lipschitz_comp_strong_L2_vector hLip hη0 hum hu hulim
  have hψ2 : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hc
  have hdψ2 : MemLp (coordinateDerivative ψ i) 2 volume :=
    (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_coordinateDerivative hc i)
  let a (j : ι) (k : ℕ) (x : Space n) := vectorPartial η j (um k x)
  let b (j : ι) (x : Space n) := vectorPartial η j (u x)
  have ham (j : ι) (k : ℕ) : AEStronglyMeasurable (a j k) volume :=
    (vectorPartial_continuous hη j).comp_aestronglyMeasurable (hum k).aestronglyMeasurable
  have hbm (j : ι) : AEStronglyMeasurable (b j) volume :=
    (vectorPartial_continuous hη j).comp_aestronglyMeasurable hu.aestronglyMeasurable
  have hab (j : ι) (k : ℕ) : ∀ᵐ x, ‖a j k x‖ ≤ (L : ℝ) :=
    Eventually.of_forall fun x => vectorPartial_bound hLip j (um k x)
  have hbb (j : ι) : ∀ᵐ x, ‖b j x‖ ≤ (L : ℝ) :=
    Eventually.of_forall fun x => vectorPartial_bound hLip j (u x)
  have hatop (j : ι) (k : ℕ) : MemLp (a j k) ∞ volume :=
    memLp_top_of_bound (ham j k) L (hab j k)
  have hbtop (j : ι) : MemLp (b j) ∞ volume :=
    memLp_top_of_bound (hbm j) L (hbb j)
  have hapsi (j : ι) (k : ℕ) : MemLp (fun x => a j k x * ψ x) 2 volume :=
    (hatop j k).mul hψ2
  have hbpsi (j : ι) : MemLp (fun x => b j x * ψ x) 2 volume :=
    (hbtop j).mul hψ2
  have halim (j : ι) : ∀ᵐ x, Tendsto (fun k => a j k x) atTop (𝓝 (b j x)) := by
    filter_upwards [hsae] with x hx
    exact (vectorPartial_continuous hη j).continuousAt.tendsto.comp hx
  have hpair (j : ι) : Tendsto (fun k => ∫ x, (a j k x * ψ x) * Fm (s k) j x)
      atTop (𝓝 (∫ x, (b j x * ψ x) * F j x)) := by
    obtain ⟨hprod, hlimit, ht⟩ := bounded_coefficient_mul_tendsto_L2
      (ham j) (hbm j) L.coe_nonneg (hab j) (hbb j) (halim j) hψ2
    have he : Tendsto (fun k => eLpNorm
        ((fun x => a j k x * ψ x) - (fun x => b j x * ψ x)) 2 volume) atTop (𝓝 0) :=
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hprod _ hlimit).mp ht
    exact tendsto_integral_mul_of_weighted_L2 hprod (fun k => hFm (s k) j) hlimit
      (Lp.memLp (F j)) he ((hFd j).comp hs.tendsto_atTop)
  have hleft := tendsto_integral_mul_of_eLpNorm_sub_tendsto_zero hηm hηu hdψ2 hηlim
  have heq (k : ℕ) : (∫ x, coordinateDerivative ψ i x * η (um k x)) =
      -(∑ j, ∫ x, (a j k x * ψ x) * Fm (s k) j x) := by
    have hmk (j : ι) : ContDiff ℝ 1 (fm (s k) j) :=
      (mollify_contDiff ((hf j).locallyIntegrable (by norm_num)) (s k)).of_le (by simp)
    have hv : ContDiff ℝ 1 (um k) := contDiff_pi.mpr hmk
    have hw := hasLocalWeakCoordinateDerivative_of_contDiff (hη.comp hv) i ψ hψ hc
    have hchain : coordinateDerivative (η ∘ um k) i =
        fun x => ∑ j, a j k x * Fm (s k) j x := by
      funext x
      exact coordinateDerivative_vector_comp hη hmk i x
    rw [hchain] at hw
    have hl : (∫ x, (η ∘ um k) x * coordinateDerivative ψ i x) =
        ∫ x, coordinateDerivative ψ i x * η (um k x) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => mul_comm _ _
    have hr : (∫ x, (∑ j, a j k x * Fm (s k) j x) * ψ x) =
        ∑ j, ∫ x, (a j k x * ψ x) * Fm (s k) j x := by
      calc
        _ = ∫ x, ∑ j, (a j k x * ψ x) * Fm (s k) j x := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by
            change (∑ j, a j k x * Fm (s k) j x) * ψ x = ∑ j, (a j k x * ψ x) * Fm (s k) j x
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = _ := integral_finsetSum Finset.univ fun j _ =>
          (hapsi j k).integrable_mul (hFm (s k) j)
    rwa [hl, hr] at hw
  have ht := tendsto_finsetSum Finset.univ fun j _ => hpair j
  have hfinal := tendsto_nhds_unique hleft (ht.neg.congr (fun k => (heq k).symm))
  have hl : (∫ x, coordinateDerivative ψ i x * (η ∘ u) x) =
      ∫ x, η (u x) * coordinateDerivative ψ i x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => mul_comm _ _
  have hr : (∑ j, ∫ x, (b j x * ψ x) * F j x) =
      ∫ x, (∑ j, b j x * F j x) * ψ x := by
    calc
      _ = ∫ x, ∑ j, (b j x * ψ x) * F j x :=
        (integral_finsetSum Finset.univ fun j _ =>
          (hbpsi j).integrable_mul (Lp.memLp (F j))).symm
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          change (∑ j, (b j x * ψ x) * F j x) = (∑ j, b j x * F j x) * ψ x
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
  rwa [hl, hr] at hfinal

end KLSConstantImprovement.ActualGlobalWeakVectorChain405

#print axioms KLSConstantImprovement.ActualGlobalWeakVectorChain405.vector_chain_of_global_L2_weak

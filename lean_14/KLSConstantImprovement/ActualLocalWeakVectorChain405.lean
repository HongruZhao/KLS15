import KLSConstantImprovement.ActualGlobalWeakVectorChain405
import KLS.LocalWeakDerivativeUniqueness

/-! Localization of the genuine multivariate weak chain rule by one
ordinary compact cutoff shared by all vector components. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff ENNReal NNReal
namespace KLSConstantImprovement.ActualLocalWeakVectorChain405
open KLS ActualVectorDifferential405 ActualGlobalWeakVectorChain405
variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem vector_composed_derivative_local_L2 {f F : ι → Space n → ℝ}
    (hf : ∀ j E, IsCompact E → MemLp (f j) 2 (volume.restrict E))
    (hFloc : ∀ j E, IsCompact E → MemLp (F j) 2 (volume.restrict E))
    {η : (ι → ℝ) → ℝ} (hη : ContDiff ℝ 1 η)
    {L : ℝ≥0} (hLip : LipschitzWith L η) (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (fun x => ∑ j, vectorPartial η j (fun a => f a x) * F j x) 2 (volume.restrict E) := by
  have hu : MemLp (fun x j => f j x) 2 (volume.restrict E) :=
    MemLp.of_eval fun j => hf j E hE
  apply memLp_finsetSum
  intro j _
  have hm : AEStronglyMeasurable (fun x => vectorPartial η j (fun a => f a x))
      (volume.restrict E) :=
    (vectorPartial_continuous hη j).comp_aestronglyMeasurable hu.aestronglyMeasurable
  have ht : MemLp (fun x => vectorPartial η j (fun a => f a x)) ∞ (volume.restrict E) :=
    memLp_top_of_bound hm L (Eventually.of_forall fun x => vectorPartial_bound hLip j _)
  exact ht.mul (hFloc j E hE)

theorem local_vector_chain_zero {f F : ι → Space n → ℝ} {i : Fin n}
    (hf : ∀ j E, IsCompact E → MemLp (f j) 2 (volume.restrict E))
    (hFloc : ∀ j E, IsCompact E → MemLp (F j) 2 (volume.restrict E))
    (hF : ∀ j, HasLocalWeakCoordinateDerivative (f j) (F j) i)
    {η : (ι → ℝ) → ℝ} (hη : ContDiff ℝ 1 η) (hη0 : η 0 = 0)
    {L : ℝ≥0} (hLip : LipschitzWith L η) :
    HasLocalWeakCoordinateDerivative (fun x => η (fun j => f j x))
      (fun x => ∑ j, vectorPartial η j (fun a => f a x) * F j x) i := by
  intro ψ hψ hc
  obtain ⟨N, hN⟩ := compact_subset_nat_ball hc
  let χ := smoothCutoff n N
  have hχ : ContDiff ℝ 1 χ := smoothCutoff_contDiff N
  have hχc : HasCompactSupport χ := smoothCutoff_hasCompactSupport N
  have hone (x : Space n) (hx : x ∈ tsupport ψ) : χ x = 1 :=
    smoothCutoff_eq_one_of_norm_le N (show ‖x‖ ≤ (N : ℝ) + 1 from
      (show ‖x‖ < (N : ℝ) + 1 by simpa using hN hx).le)
  have hzero (x : Space n) (hx : x ∈ tsupport ψ) : coordinateDerivative χ i x = 0 :=
    coordinateDerivative_smoothCutoff_eq_zero_of_norm_lt N i
      (show ‖x‖ < (N : ℝ) + 1 by simpa using hN hx)
  have hex (j : ι) := (hF j).compact_mul (hf j) (hFloc j) hχ hχc
  choose W hW hWe using hex
  have hcf (j : ι) : MemLp (fun x => χ x * f j x) 2 volume :=
    memLp_compact_mul_of_local hχ.continuous hχc (hf j)
  have hw := vector_chain_of_global_L2_weak hcf hW hη hη0 hLip ψ hψ hc
  have hv (x : Space n) (hx : x ∈ tsupport ψ) :
      (fun j => χ x * f j x) = fun j => f j x := by
    funext j
    rw [hone x hx, one_mul]
  have hl : (∫ x, η (fun j => χ x * f j x) * coordinateDerivative ψ i x) =
      ∫ x, η (fun j => f j x) * coordinateDerivative ψ i x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change η (fun j => χ x * f j x) * coordinateDerivative ψ i x =
        η (fun j => f j x) * coordinateDerivative ψ i x
      by_cases hs : x ∈ tsupport ψ
      · rw [hv x hs]
      · have hd : coordinateDerivative ψ i x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun ht => hs (tsupport_coordinateDerivative_subset ψ i ht))
        rw [hd, mul_zero, mul_zero]
  have hr : (∫ x, (∑ j, vectorPartial η j (fun a => χ x * f a x) * W j x) * ψ x) =
      ∫ x, (∑ j, vectorPartial η j (fun a => f a x) * F j x) * ψ x := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hWe] with x hx
    by_cases hs : x ∈ tsupport ψ
    · rw [hv x hs]
      apply congrArg (fun z : ℝ => z * ψ x)
      apply Finset.sum_congr rfl
      intro j _
      rw [hx j, hone x hs, hzero x hs, one_mul, zero_mul, add_zero]
    · rw [image_eq_zero_of_notMem_tsupport hs, mul_zero, mul_zero]
  rwa [hl, hr] at hw

theorem local_vector_chain {f F : ι → Space n → ℝ} {i : Fin n}
    (hf : ∀ j E, IsCompact E → MemLp (f j) 2 (volume.restrict E))
    (hFloc : ∀ j E, IsCompact E → MemLp (F j) 2 (volume.restrict E))
    (hF : ∀ j, HasLocalWeakCoordinateDerivative (f j) (F j) i)
    {η : (ι → ℝ) → ℝ} (hη : ContDiff ℝ 1 η)
    {L : ℝ≥0} (hLip : LipschitzWith L η) :
    HasLocalWeakCoordinateDerivative (fun x => η (fun j => f j x))
      (fun x => ∑ j, vectorPartial η j (fun a => f a x) * F j x) i := by
  let η₀ : (ι → ℝ) → ℝ := fun v => η v - η 0
  have hη₀ : ContDiff ℝ 1 η₀ := hη.sub contDiff_const
  have hη₀0 : η₀ 0 = 0 := sub_self _
  have hLip₀ : LipschitzWith L η₀ := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    rw [dist_eq_norm, dist_eq_norm]
    have he : η₀ v - η₀ w = η v - η w := by dsimp [η₀]; ring
    rw [he]
    exact hLip.norm_sub_le v w
  have hpart (j : ι) : vectorPartial η₀ j = vectorPartial η j := by
    funext v
    dsimp only [vectorPartial, η₀]
    rw [fderiv_sub_const]
  have hw := local_vector_chain_zero hf hFloc hF hη₀ hη₀0 hLip₀
  have hval : LocallyIntegrable (fun x => η₀ (fun j => f j x)) volume := by
    apply locallyIntegrable_of_memLp_two_on_compacts
    intro E hE
    exact hLip₀.comp_memLp hη₀0 (MemLp.of_eval fun j => hf j E hE)
  have hder : LocallyIntegrable (fun x => ∑ j, vectorPartial η₀ j (fun a => f a x) * F j x) volume :=
    locallyIntegrable_of_memLp_two_on_compacts
      (vector_composed_derivative_local_L2 hf hFloc hη₀ hLip₀)
  have hcval : LocallyIntegrable (fun _ : Space n => η 0) volume := locallyIntegrable_const _
  have hczero : LocallyIntegrable (fun _ : Space n => (0 : ℝ)) volume := locallyIntegrable_const _
  have hadd := hw.add (hasLocalWeakCoordinateDerivative_const (η 0) i) hval hcval hder hczero
  refine hadd.congr_ae (Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · dsimp only [η₀]
    ring
  · simp only [hpart, add_zero]

end KLSConstantImprovement.ActualLocalWeakVectorChain405

#print axioms KLSConstantImprovement.ActualLocalWeakVectorChain405.vector_composed_derivative_local_L2
#print axioms KLSConstantImprovement.ActualLocalWeakVectorChain405.local_vector_chain

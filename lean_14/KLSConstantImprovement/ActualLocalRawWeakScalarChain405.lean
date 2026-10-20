import KLSConstantImprovement.ActualRawWeakScalarChain405

/-!
Localization of the actual raw H1 scalar chain rule. A genuine compact
ordinary cutoff is identically one on the support of each weak test,
and its derivative is zero there. No local Lipschitz representative of
the raw function is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ContDiff Topology NNReal ENNReal
namespace KLSConstantImprovement.ActualLocalRawWeakScalarChain405
open KLS ActualRawWeakScalarChain405
variable {n : ℕ}

theorem local_scalar_chain {f F : Space n → ℝ} {i : Fin n}
    (hf : ∀ E, IsCompact E → MemLp f 2 (volume.restrict E))
    (hFloc : ∀ E, IsCompact E → MemLp F 2 (volume.restrict E))
    (hF : HasLocalWeakCoordinateDerivative f F i)
    {η : ℝ → ℝ} (hη : ContDiff ℝ 1 η) (hη0 : η 0 = 0)
    {L D : ℝ≥0} (hLip : LipschitzWith L η) (hDLip : LipschitzWith D (deriv η)) :
    HasLocalWeakCoordinateDerivative (η ∘ f) (fun x => deriv η (f x) * F x) i := by
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
  obtain ⟨W, hW, hWe⟩ := hF.compact_mul hf hFloc hχ hχc
  have hcf : MemLp (fun x => χ x * f x) 2 volume :=
    memLp_compact_mul_of_local hχ.continuous hχc hf
  have hw := scalar_chain_of_global_L2_weak hcf hW hη hη0 hLip hDLip ψ hψ hc
  have hl : (∫ x, (η ∘ (fun y => χ y * f y)) x * coordinateDerivative ψ i x) =
      ∫ x, (η ∘ f) x * coordinateDerivative ψ i x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change η (χ x * f x) * coordinateDerivative ψ i x = η (f x) * coordinateDerivative ψ i x
      by_cases hs : x ∈ tsupport ψ
      · rw [hone x hs, one_mul]
      · have hd : coordinateDerivative ψ i x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun ht => hs (tsupport_coordinateDerivative_subset ψ i ht))
        rw [hd, mul_zero, mul_zero]
  have hr : (∫ x, (deriv η (χ x * f x) * W x) * ψ x) =
      ∫ x, (deriv η (f x) * F x) * ψ x := by
    apply integral_congr_ae
    filter_upwards [hWe] with x hx
    by_cases hs : x ∈ tsupport ψ
    · rw [hx, hone x hs, hzero x hs, one_mul, zero_mul, add_zero, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hs, mul_zero, mul_zero]
  rwa [hl, hr] at hw

end KLSConstantImprovement.ActualLocalRawWeakScalarChain405

#print axioms KLSConstantImprovement.ActualLocalRawWeakScalarChain405.local_scalar_chain

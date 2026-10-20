import KLSConstantImprovement.ActualCompactRawH1Rellich405

/-! The compact raw-H1 estimate gives an actual totally bounded L2 range.
This form permits one common subsequence for countably many localizations. -/
noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators ENNReal
namespace KLSConstantImprovement.ActualCompactRawH1Precompact405
open KLS ActualCompactRawH1Rellich405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem compact_raw_H1_totallyBounded
    {f : ℕ → Space n → ℝ} {D : ℕ → Fin n → Space n → ℝ}
    (hf : ∀ k, MemLp (f k) 2 volume) (hD : ∀ k i, MemLp (D k i) 2 volume)
    (hw : ∀ k i, HasLocalWeakCoordinateDerivative (f k) (D k i) i)
    {R A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hs : ∀ k, tsupport (f k) ⊆ closedBall (0 : Space n) R)
    (hv : ∀ k, (∫ x, f k x ^ 2) ≤ A)
    (hd : ∀ k i, (∫ x, D k i x ^ 2) ≤ B) :
    TotallyBounded (range (fun k => (hf k).toLp (f k))) := by
  let F (k : ℕ) : Lp ℝ 2 volume := (hf k).toLp (f k)
  let G (k : ℕ) (i : Fin n) : Lp ℝ 2 volume := (hD k i).toLp (D k i)
  have hFn (k : ℕ) : ‖F k‖ ≤ Real.sqrt A := by
    apply (Real.le_sqrt (norm_nonneg _) hA).mpr
    rw [MeasureTheory.norm_sq_eq_integral_sq]
    rw [integral_congr_ae ((hf k).coeFn_toLp.mono (fun x hx => congrArg (fun z : ℝ => z^2) hx))]
    exact hv k
  have hGn (k : ℕ) (i : Fin n) : ‖G k i‖ ≤ Real.sqrt B := by
    apply (Real.le_sqrt (norm_nonneg _) hB).mpr
    rw [MeasureTheory.norm_sq_eq_integral_sq]
    rw [integral_congr_ae ((hD k i).coeFn_toLp.mono (fun x hx => congrArg (fun z : ℝ => z^2) hx))]
    exact hd k i
  change TotallyBounded (range F)
  apply EllipticPdes.Analysis.totallyBounded_of_lipschitz_translation
    (R := R) (M := Real.sqrt A) (Λ := n*Real.sqrt B)
  · rintro _ ⟨k, rfl⟩
    exact hFn k
  · rintro _ ⟨k, rfl⟩
    filter_upwards [(hf k).coeFn_toLp] with x hx
    intro hxR
    rw [hx]
    exact image_eq_zero_of_notMem_tsupport (fun hxs => hxR (hs k hxs))
  · rintro _ ⟨k, rfl⟩ h
    have hwF (i : Fin n) : HasLocalWeakCoordinateDerivative
        (F k : Space n → ℝ) (G k i) i :=
      (hw k i).congr_ae (hf k).coeFn_toLp.symm (hD k i).coeFn_toLp.symm
    have hsF : ∀ᵐ x ∂(volume : Measure (Space n)),
        x ∉ closedBall (0 : Space n) R → F k x = 0 := by
      filter_upwards [(hf k).coeFn_toLp] with x hx
      intro hxR
      rw [hx]
      exact image_eq_zero_of_notMem_tsupport (fun hxs => hxR (hs k hxs))
    exact (compact_raw_translation_bound (F k) (G k) hwF hsF h).trans
      (mul_le_mul_of_nonneg_right
        (by simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
          Finset.sum_le_sum (s := Finset.univ) (fun i _ => hGn k i)) (norm_nonneg h))

end KLSConstantImprovement.ActualCompactRawH1Precompact405
#print axioms KLSConstantImprovement.ActualCompactRawH1Precompact405.compact_raw_H1_totallyBounded

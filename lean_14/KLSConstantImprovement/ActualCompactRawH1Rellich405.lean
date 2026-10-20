import KLSConstantImprovement.ActualLocalRawWeakMollification405
import KLS.CompactC1L2Subsequence

/-! Actual compact raw-H1 Rellich compactness. The translation bound is
proved by the same concrete mollifiers, their L2 contraction, and genuine
weak derivative commutation. No scalar strong operator core is used. -/
noncomputable section
open MeasureTheory Filter Set Metric InnerProductSpace ContinuousLinearMap
open scoped Topology BigOperators ContDiff ENNReal Convolution
namespace KLSConstantImprovement.ActualCompactRawH1Rellich405
open KLS ActualLocalRawWeakMollification405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem mollify_support_closedBall_ae {f : Space n → ℝ} {R : ℝ}
    (hs : ∀ᵐ y ∂(volume : Measure (Space n)), y ∉ closedBall (0 : Space n) R → f y = 0) (k : ℕ) :
    tsupport (mollify k f) ⊆ closedBall (0 : Space n) (R + 2) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hxout
  apply hx
  unfold mollify scalarConvolution
  rw [convolution_def]
  apply integral_eq_zero_of_ae
  filter_upwards [hs] with y hy
  show (lsmul ℝ ℝ) (f y) (mollifierKernel n k (x - y)) = 0
  by_cases hfy : f y = 0
  · simp [hfy]
  have hyR : y ∈ closedBall (0 : Space n) R := by
    by_contra hh
    exact hfy (hy hh)
  have hy : ‖y‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hyR
  have hκ : mollifierKernel n k (x - y) = 0 := by
    by_contra hκ
    have hnorm : ‖x - y‖ ≤ 2 := by
      simpa only [mem_closedBall, dist_zero_right] using
        mollifierKernel_support_subset k hκ
    have hxnorm := norm_le_norm_sub_add x y
    apply hxout
    simp only [mem_closedBall, dist_zero_right]
    linarith
  simp [hκ]

theorem compact_raw_translation_bound (f : Lp ℝ 2 (volume : Measure (Space n)))
    (D : Fin n → Lp ℝ 2 (volume : Measure (Space n)))
    (hw : ∀ i, HasLocalWeakCoordinateDerivative (f : Space n → ℝ) (D i) i)
    {R : ℝ} (hs : ∀ᵐ x ∂(volume : Measure (Space n)),
      x ∉ closedBall (0 : Space n) R → f x = 0)
    (h : Space n) :
    ‖transL2 h f - f‖ ≤ (∑ i, ‖D i‖) * ‖h‖ := by
  have hloc : LocallyIntegrable (f : Space n → ℝ) volume :=
    locallyIntegrable_of_memLp_two_on_compacts (fun E _ => (Lp.memLp f).restrict E)
  let F (k : ℕ) : Lp ℝ 2 (volume : Measure (Space n)) :=
    (memLp_mollify (Lp.memLp f) k).toLp (mollify k f)
  let G (k : ℕ) (i : Fin n) : Lp ℝ 2 (volume : Measure (Space n)) :=
    (memLp_mollify (Lp.memLp (D i)) k).toLp (mollify k (D i))
  have hFn : Tendsto F atTop (𝓝 f) := by
    have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun k => mollify k f)
      (fun k => memLp_mollify (Lp.memLp f) k) f (Lp.memLp f)).mpr
      (eLpNorm_mollify_sub_tendsto_zero (Lp.memLp f))
    simpa only [Lp.toLp_coeFn, F] using ht
  have hGn (k : ℕ) (i : Fin n) : ‖G k i‖ ≤ ‖D i‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [MeasureTheory.norm_sq_eq_integral_sq, MeasureTheory.norm_sq_eq_integral_sq]
    have he : (∫ x, G k i x ^ 2) = ∫ x, mollify k (D i) x ^ 2 :=
      integral_congr_ae ((memLp_mollify (Lp.memLp (D i)) k).coeFn_toLp.mono
        (fun x hx => congrArg (fun z : ℝ => z ^ 2) hx))
    rw [he]
    exact integral_sq_mollify_le (Lp.memLp (D i)) k
  have hbound (k : ℕ) : ‖transL2 h (F k) - F k‖ ≤ (∑ i, ‖D i‖) * ‖h‖ := by
    have hc : HasCompactSupport (mollify k (f : Space n → ℝ)) :=
      (isCompact_closedBall (0 : Space n) (R + 2)).of_isClosed_subset
        (isClosed_tsupport _) (mollify_support_closedBall_ae hs k)
    have he := compact_translation_bound_of_smooth
      ((mollify_contDiff hloc k).of_le (by simp)) hc (F k) (G k)
      (memLp_mollify (Lp.memLp f) k).coeFn_toLp
      (fun i => by
        rw [local_weak_mollify_eq hloc (hw i) k]
        exact (memLp_mollify (Lp.memLp (D i)) k).coeFn_toLp) h
    exact he.trans (mul_le_mul_of_nonneg_right
      (Finset.sum_le_sum fun i _ => hGn k i) (norm_nonneg h))
  have ht : Tendsto (fun k => ‖transL2 h (F k) - F k‖) atTop
      (𝓝 ‖transL2 h f - f‖) :=
    (((transL2 h).continuous.tendsto f).comp hFn).sub hFn |>.norm
  exact le_of_tendsto ht (Eventually.of_forall hbound)

theorem exists_strong_L2_subsequence_compact_raw
    {f : ℕ → Space n → ℝ} {D : ℕ → Fin n → Space n → ℝ}
    (hf : ∀ k, MemLp (f k) 2 volume) (hD : ∀ k i, MemLp (D k i) 2 volume)
    (hw : ∀ k i, HasLocalWeakCoordinateDerivative (f k) (D k i) i)
    {R A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hs : ∀ k, tsupport (f k) ⊆ closedBall (0 : Space n) R)
    (hv : ∀ k, (∫ x, f k x ^ 2) ≤ A)
    (hd : ∀ k i, (∫ x, D k i x ^ 2) ≤ B) :
    ∃ (g : Lp ℝ 2 (volume : Measure (Space n))) (σ : ℕ → ℕ),
      StrictMono σ ∧ Tendsto (fun k => eLpNorm
        (f (σ k) - (g : Space n → ℝ)) 2 volume) atTop (𝓝 0) := by
  let F (k : ℕ) : Lp ℝ 2 volume := (hf k).toLp (f k)
  let G (k : ℕ) (i : Fin n) : Lp ℝ 2 volume := (hD k i).toLp (D k i)
  have hFn (k : ℕ) : ‖F k‖ ≤ Real.sqrt A := by
    apply (Real.le_sqrt (norm_nonneg _) hA).mpr
    rw [MeasureTheory.norm_sq_eq_integral_sq]
    rw [integral_congr_ae ((hf k).coeFn_toLp.mono
      (fun x hx => congrArg (fun z : ℝ => z ^ 2) hx))]
    exact hv k
  have hGn (k : ℕ) (i : Fin n) : ‖G k i‖ ≤ Real.sqrt B := by
    apply (Real.le_sqrt (norm_nonneg _) hB).mpr
    rw [MeasureTheory.norm_sq_eq_integral_sq]
    rw [integral_congr_ae ((hD k i).coeFn_toLp.mono
      (fun x hx => congrArg (fun z : ℝ => z ^ 2) hx))]
    exact hd k i
  have htb : TotallyBounded (range F) := by
    apply EllipticPdes.Analysis.totallyBounded_of_lipschitz_translation
      (R := R) (M := Real.sqrt A) (Λ := n * Real.sqrt B)
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
      have he := compact_raw_translation_bound (F k) (G k) hwF hsF h
      apply he.trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg h)
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
        Finset.sum_le_sum (s := Finset.univ) (fun i _ => hGn k i)
  obtain ⟨g, _, σ, hσ, hconv⟩ := htb.closure.isCompact_of_isClosed
    isClosed_closure |>.tendsto_subseq (fun k => subset_closure (mem_range_self k))
  refine ⟨g, σ, hσ, ?_⟩
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun k => f (σ k))
    (fun k => hf (σ k)) g (Lp.memLp g)).mp
  simpa only [Lp.toLp_coeFn, F, Function.comp_def] using hconv

end KLSConstantImprovement.ActualCompactRawH1Rellich405
#print axioms KLSConstantImprovement.ActualCompactRawH1Rellich405.mollify_support_closedBall_ae
#print axioms KLSConstantImprovement.ActualCompactRawH1Rellich405.compact_raw_translation_bound
#print axioms KLSConstantImprovement.ActualCompactRawH1Rellich405.exists_strong_L2_subsequence_compact_raw

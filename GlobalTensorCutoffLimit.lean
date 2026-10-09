import HigherCutoffBounds

/-! Global all-order weighted L² convergence of the literal expanding
cutoff Leibniz jets of an actual primitive tower. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n r : ℕ} {φ : Space n → ℝ}

lemma maskedDirections_false (I : Fin r → Fin n) :
    maskedDirections I (fun _ => false) = [] := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [maskedDirections, Bool.false_eq_true, ↓reduceIte]
    change maskedDirections (Fin.tail I) (fun _ => false) = []
    exact ih (Fin.tail I)

lemma maskedDirections_true (I : Fin r → Fin n) :
    maskedDirections I (fun _ => true) = List.ofFn I := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [maskedDirections, ↓reduceIte, List.ofFn_succ]
    change I 0 :: maskedDirections (Fin.tail I) (fun _ => true) = I 0 :: List.ofFn (Fin.tail I)
    exact congrArg (List.cons (I 0)) (ih (Fin.tail I))

lemma maskedDirections_eq_nil_iff (I : Fin r → Fin n) (b : Fin r → Bool) :
    maskedDirections I b = [] ↔ ∀ j, b j = false := by
  induction r with
  | zero => simp [maskedDirections]
  | succ r ih =>
    cases hb : b 0 with
    | false =>
      simp only [maskedDirections, hb, Bool.false_eq_true, ↓reduceIte, ih]
      constructor
      · intro ht j
        exact Fin.cases hb ht j
      · intro ht j
        exact ht j.succ
    | true =>
      simp only [maskedDirections, hb, ↓reduceIte, List.cons_ne_self, List.cons_ne_nil, false_iff]
      intro ht
      simpa only [hb, Bool.true_eq_false] using ht 0

lemma tensorWordLp_ofFn (U : (k : ℕ) → OrderedTensorField φ k) (I : OrderedTensorIndex n r) :
    tensorWordLp U (List.ofFn I) = U r I :=
  congrArg (fun p : Σ k : ℕ, OrderedTensorIndex n k => U p.1 p.2)
    ((List.equivSigmaTuple (α := Fin n)).apply_symm_apply ⟨r, I⟩)

theorem tensorCutoffJet_smoothCutoff_tendsto (U : (k : ℕ) → OrderedTensorField φ k)
    (r : ℕ) (I : OrderedTensorIndex n r) (x : Space n) :
    Tendsto (fun k => tensorCutoffJet U (smoothCutoff n k) r I x) atTop (𝓝 (U r I x)) := by
  have ht (b : Fin r → Bool) :
      Tendsto (fun k => coordinateWordDerivative (smoothCutoff n k) (maskedDirections I b) x *
        tensorWordLp U (maskedDirections I (fun j => !(b j))) x) atTop
        (𝓝 (if b = (fun _ => false) then U r I x else 0)) := by
    by_cases hb : b = (fun _ => false)
    · subst b
      simpa only [maskedDirections_false, coordinateWordDerivative, List.map_nil,
        directionalWordDerivative_nil, Bool.not_false, maskedDirections_true, tensorWordLp_ofFn,
        ↓reduceIte, one_mul] using (smoothCutoff_tendsto_one x).mul_const (U r I x)
    · have hne : maskedDirections I b ≠ [] := by
        intro he
        apply hb
        funext j
        exact (maskedDirections_eq_nil_iff I b).mp he j
      simpa only [if_neg hb, zero_mul] using
        (smoothCutoff_coordinateWord_tendsto_zero _ hne x).mul_const
          (tensorWordLp U (maskedDirections I (fun j => !(b j))) x)
  have hs := tendsto_finsetSum Finset.univ (fun b _ => ht b)
  simpa only [tensorCutoffJet, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] using hs

lemma eLpNorm_tendsto_zero_of_L2_pointwise_bound {μ : Measure (Space n)}
    {f : ℕ → Space n → ℝ} {G : Space n → ℝ} (hG : MemLp G 2 μ)
    (hm : ∀ k, AEStronglyMeasurable (f k) μ)
    (hb : ∀ k x, ‖f k x‖ ≤ ‖G x‖)
    (ht : ∀ x, Tendsto (fun k => f k x) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (f k) 2 μ) atTop (𝓝 0) := by
  have hf (k : ℕ) : MemLp (f k) 2 μ := hG.norm.mono' (hm k) (Eventually.of_forall (hb k))
  apply tendsto_eLpNorm_zero_of_integral_sq hf
  have hs (k : ℕ) (x : Space n) : ‖f k x ^ 2‖ ≤ G x ^ 2 := by
    have he := (sq_le_sq₀ (norm_nonneg (f k x)) (norm_nonneg (G x))).mpr (hb k x)
    change |f k x ^ 2| ≤ G x ^ 2
    rw [abs_of_nonneg (sq_nonneg (f k x))]
    simpa only [Real.norm_eq_abs, sq_abs] using he
  have hi := tendsto_integral_of_dominated_convergence (fun x => G x ^ 2)
    (fun k => (hm k).pow 2) hG.integrable_sq
    (fun k => Eventually.of_forall (hs k))
    (Eventually.of_forall fun x => by simpa using (ht x).pow 2)
  simpa only [integral_zero, Pi.pow_apply] using hi

theorem eLpNorm_tensorCutoffJet_smoothCutoff_sub_tendsto_zero
    (U : (k : ℕ) → OrderedTensorField φ k) (r : ℕ) (I : OrderedTensorIndex n r) :
    Tendsto (fun k => eLpNorm
      (fun x => tensorCutoffJet U (smoothCutoff n k) r I x - U r I x)
        2 (potentialMeasure φ)) atTop (𝓝 0) := by
  choose K hK hb using fun b : Fin r → Bool =>
    smoothCutoff_coordinateWord_uniform_bound (maskedDirections I b)
  let G : Space n → ℝ := fun x =>
    (∑ b : Fin r → Bool, K b * ‖tensorWordLp U (maskedDirections I (fun j => !(b j))) x‖) +
      ‖U r I x‖
  have hG : MemLp G 2 (potentialMeasure φ) := by
    apply MemLp.add
    · apply memLp_finsetSum Finset.univ
      intro b _
      exact (Lp.memLp (tensorWordLp U (maskedDirections I (fun j => !(b j))))).norm.const_mul (K b)
    · exact (Lp.memLp (U r I)).norm
  have hm (k : ℕ) : AEStronglyMeasurable
      (fun x => tensorCutoffJet U (smoothCutoff n k) r I x - U r I x) (potentialMeasure φ) := by
    apply AEStronglyMeasurable.sub
    · apply Finset.aestronglyMeasurable_fun_sum
      intro b _
      exact (coordinateWordDerivative_contDiff (smoothCutoff_contDiff_top k) _).continuous.aestronglyMeasurable.mul
        (Lp.memLp (tensorWordLp U (maskedDirections I (fun j => !(b j))))).aestronglyMeasurable
    · exact (Lp.memLp (U r I)).aestronglyMeasurable
  apply eLpNorm_tendsto_zero_of_L2_pointwise_bound hG hm
  · intro k x
    calc
      _ ≤ ‖tensorCutoffJet U (smoothCutoff n k) r I x‖ + ‖U r I x‖ := norm_sub_le _ _
      _ ≤ G x := by
        change ‖tensorCutoffJet U (smoothCutoff n k) r I x‖ + ‖U r I x‖ ≤
          (∑ b : Fin r → Bool, K b * ‖tensorWordLp U (maskedDirections I (fun j => !(b j))) x‖) +
            ‖U r I x‖
        refine add_le_add ?_ le_rfl
        unfold tensorCutoffJet
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun b _ => ?_))
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hb b k x) (norm_nonneg _)
      _ ≤ ‖G x‖ := le_abs_self _
  · intro x
    simpa only [sub_self] using (tensorCutoffJet_smoothCutoff_tendsto U r I x).sub_const (U r I x)

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorCutoffJet_smoothCutoff_tendsto
#print axioms KLS.DeterministicBridgeIntegration.eLpNorm_tensorCutoffJet_smoothCutoff_sub_tendsto_zero

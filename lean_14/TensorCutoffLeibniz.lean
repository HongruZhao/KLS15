import TensorWeakDerivativeTower

/-! Literal all-order cutoff jets, with labeled Boolean masks retaining
the correct multiplicities of repeated coordinate directions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace
namespace KLS.DeterministicBridgeIntegration
variable {n r s : ℕ} {φ χ : Space n → ℝ}

def coordinateWordDerivative (χ : Space n → ℝ) (L : List (Fin n)) : Space n → ℝ :=
  directionalWordDerivative χ (L.map (fun i => EuclideanSpace.single i 1))

lemma coordinateWordDerivative_cons (χ : Space n → ℝ) (L : List (Fin n)) (i : Fin n) :
    coordinateWordDerivative χ (i :: L) = coordinateDerivative (coordinateWordDerivative χ L) i := by
  funext x
  simp only [coordinateWordDerivative, List.map_cons, directionalWordDerivative_cons,
    coordinateDerivative]

lemma coordinateWordDerivative_contDiff (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (L : List (Fin n)) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateWordDerivative χ L) :=
  contDiff_directionalWordDerivative hχ _

lemma coordinateWordDerivative_hasCompactSupport (hc : HasCompactSupport χ) (L : List (Fin n)) :
    HasCompactSupport (coordinateWordDerivative χ L) := by
  induction L with
  | nil => simpa only [coordinateWordDerivative, List.map_nil, directionalWordDerivative_nil] using hc
  | cons i L ih =>
    rw [coordinateWordDerivative_cons]
    exact hasCompactSupport_coordinateDerivative ih i

lemma maskedDirections_length_le {m : ℕ} (I : Fin m → Fin n) (b : Fin m → Bool) :
    (maskedDirections I b).length ≤ m := by
  induction m with
  | zero => simp [maskedDirections]
  | succ m ih =>
    simp only [maskedDirections]
    split
    · exact Nat.succ_le_succ (ih (Fin.tail I) (Fin.tail b))
    · exact (ih (Fin.tail I) (Fin.tail b)).trans (Nat.le_succ m)

def tensorCutoffJet (U : (k : ℕ) → OrderedTensorField φ k) (χ : Space n → ℝ)
    (r : ℕ) (I : OrderedTensorIndex n r) (x : Space n) : ℝ :=
  ∑ b : Fin r → Bool, coordinateWordDerivative χ (maskedDirections I b) x *
    tensorWordLp U (maskedDirections I (fun j => !(b j))) x

lemma tensorCutoffJet_cons (U : (k : ℕ) → OrderedTensorField φ k)
    (χ : Space n → ℝ) (I : OrderedTensorIndex n r) (i : Fin n) :
    tensorCutoffJet U χ (r + 1) (Fin.cons i I) = fun x =>
      ∑ b : Fin r → Bool,
        (coordinateWordDerivative χ (maskedDirections I b) x *
          tensorWordLp U (i :: maskedDirections I (fun j => !(b j))) x +
        coordinateDerivative (coordinateWordDerivative χ (maskedDirections I b)) i x *
          tensorWordLp U (maskedDirections I (fun j => !(b j))) x) := by
  funext x
  unfold tensorCutoffJet
  rw [sum_bool_masks]
  simp only [complement_fin_cons, maskedDirections, Fin.cons_zero, Fin.tail_cons,
    Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.not_false]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [coordinateWordDerivative_cons]
  ring

lemma tensorCutoffJet_memLp (hφ : Continuous φ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (U : (k : ℕ) → OrderedTensorField φ k)
    (r : ℕ) (I : OrderedTensorIndex n r) : MemLp (tensorCutoffJet U χ r I) 2 volume := by
  unfold tensorCutoffJet
  apply memLp_finsetSum Finset.univ
  intro b _
  exact memLp_compact_mul_of_local (coordinateWordDerivative_contDiff hχ _).continuous
    (coordinateWordDerivative_hasCompactSupport hc _)
    (fun K hK => tensorWordLp_memLp_restrict hφ U _ hK)

/-- Every literal cutoff jet has the next labeled Leibniz jet as its actual
Lebesgue L² weak derivative. The hypothesis is the already constructed
centered H¹ representative tower, not a compact-core assumption. -/
theorem tensorCutoffJet_hasWeakCoordinateDerivative (hφ : ContDiff ℝ 1 φ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (U : (k : ℕ) → OrderedTensorField φ k)
    (hgraph : ∀ k, k < s → ∃ V : TensorPrimitive (φ := φ) (OrderedTensorIndex n k),
      finitePrimitiveValue (OrderedTensorIndex n k) V = U k ∧
        ∀ I i, weightedH1Derivative φ i (V I) = U (k + 1) (Fin.cons i I))
    (hr : r < s) (I : OrderedTensorIndex n r) (i : Fin n) :
    HasWeakCoordinateDerivative (tensorCutoffJet U χ r I) i
      ((tensorCutoffJet_memLp hφ.continuous hχ hc U (r + 1) (Fin.cons i I)).toLp
        (tensorCutoffJet U χ (r + 1) (Fin.cons i I))) := by
  let A (b : Fin r → Bool) : Space n → ℝ := fun x =>
    coordinateWordDerivative χ (maskedDirections I b) x *
      tensorWordLp U (maskedDirections I (fun j => !(b j))) x
  let D (b : Fin r → Bool) : Space n → ℝ := fun x =>
    coordinateWordDerivative χ (maskedDirections I b) x *
      tensorWordLp U (i :: maskedDirections I (fun j => !(b j))) x +
    coordinateDerivative (coordinateWordDerivative χ (maskedDirections I b)) i x *
      tensorWordLp U (maskedDirections I (fun j => !(b j))) x
  have hA (b : Fin r → Bool) : MemLp (A b) 2 volume :=
    memLp_compact_mul_of_local (coordinateWordDerivative_contDiff hχ _).continuous
      (coordinateWordDerivative_hasCompactSupport hc _)
      (fun K hK => tensorWordLp_memLp_restrict hφ.continuous U _ hK)
  have hD (b : Fin r → Bool) : MemLp (D b) 2 volume := by
    apply MemLp.add
    · exact memLp_compact_mul_of_local (coordinateWordDerivative_contDiff hχ _).continuous
        (coordinateWordDerivative_hasCompactSupport hc _)
        (fun K hK => tensorWordLp_memLp_restrict hφ.continuous U _ hK)
    · rw [← coordinateWordDerivative_cons]
      exact memLp_compact_mul_of_local (coordinateWordDerivative_contDiff hχ _).continuous
        (coordinateWordDerivative_hasCompactSupport hc _)
        (fun K hK => tensorWordLp_memLp_restrict hφ.continuous U _ hK)
  intro ψ hψ hψc
  have hψLp : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
  have hdψLp : MemLp (coordinateDerivative ψ i) 2 volume :=
    (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_coordinateDerivative hψc i)
  have hw (b : Fin r → Bool) :
      (∫ x, A b x * coordinateDerivative ψ i x) = -(∫ x, D b x * ψ x) := by
    obtain ⟨_, g, hg, hw⟩ := tensorWordLp_compact_product hφ U hgraph
      (maskedDirections I (fun j => !(b j)))
      ((maskedDirections_length_le I _).trans_lt hr) i
      ((coordinateWordDerivative_contDiff hχ _).of_le (by simp))
      (coordinateWordDerivative_hasCompactSupport hc _)
    have he := hw ψ hψ hψc
    change (∫ x, A b x * coordinateDerivative ψ i x) = -(∫ x, g x * ψ x) at he
    rw [he]
    congr 1
    exact integral_congr_ae (hg.fun_mul EventuallyEq.rfl)
  calc
    _ = ∫ x, ∑ b : Fin r → Bool, A b x * coordinateDerivative ψ i x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by simp only [tensorCutoffJet, A, Finset.sum_mul]
    _ = ∑ b : Fin r → Bool, ∫ x, A b x * coordinateDerivative ψ i x :=
      integral_finsetSum Finset.univ (fun b _ => (hA b).integrable_mul hdψLp)
    _ = ∑ b : Fin r → Bool, -(∫ x, D b x * ψ x) := Finset.sum_congr rfl (fun b _ => hw b)
    _ = -(∫ x, ∑ b : Fin r → Bool, D b x * ψ x) := by
      have he : (∫ x, ∑ b : Fin r → Bool, D b x * ψ x) =
          ∑ b : Fin r → Bool, ∫ x, D b x * ψ x :=
        integral_finsetSum Finset.univ (fun b _ => (hD b).integrable_mul hψLp)
      rw [he, Finset.sum_neg_distrib]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [(tensorCutoffJet_memLp hφ.continuous hχ hc U (r + 1)
        (Fin.cons i I)).coeFn_toLp] with x hx
      rw [hx, tensorCutoffJet_cons]
      simp only [D, Finset.sum_mul]

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorCutoffJet_cons
#print axioms KLS.DeterministicBridgeIntegration.tensorCutoffJet_memLp
#print axioms KLS.DeterministicBridgeIntegration.tensorCutoffJet_hasWeakCoordinateDerivative

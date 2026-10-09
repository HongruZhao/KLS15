import TensorCutoffLeibniz
import KLS.CompactRawWeakDerivative

/-! Literal Leibniz jets of a locally L2 raw weak derivative tower. This
version does not require global integrability of the highest derivative. -/
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n s r : ℕ}
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def rawCutoffJet (J : List (Fin n) → Space n → ℝ) (χ : Space n → ℝ)
    (r : ℕ) (I : Fin r → Fin n) (x : Space n) : ℝ :=
  ∑ b : Fin r → Bool, coordinateWordDerivative χ (maskedDirections I b) x*
    J (maskedDirections I (fun j => !(b j))) x

theorem rawCutoffJet_cons (J : List (Fin n) → Space n → ℝ) (χ : Space n → ℝ)
    (I : Fin r → Fin n) (i : Fin n) :
    rawCutoffJet J χ (r+1) (Fin.cons i I) = fun x => ∑ b : Fin r → Bool,
      (coordinateWordDerivative χ (maskedDirections I b) x*
        J (i::maskedDirections I (fun j => !(b j))) x+
      coordinateDerivative (coordinateWordDerivative χ (maskedDirections I b)) i x*
        J (maskedDirections I (fun j => !(b j))) x) := by
  funext x
  unfold rawCutoffJet
  rw [sum_bool_masks]
  simp only [complement_fin_cons,maskedDirections,Fin.cons_zero,Fin.tail_cons,
    Bool.false_eq_true,↓reduceIte,Bool.not_true,Bool.not_false]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [coordinateWordDerivative_cons]
  ring

theorem rawCutoffJet_memLp (J : List (Fin n) → Space n → ℝ)
    (hloc : ∀ L, L.length ≤ s → ∀ K : Set (Space n), IsCompact K →
      MemLp (J L) 2 (volume.restrict K))
    {χ : Space n → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hr : r ≤ s) (I : Fin r → Fin n) : MemLp (rawCutoffJet J χ r I) 2 volume := by
  unfold rawCutoffJet
  apply memLp_finsetSum Finset.univ
  intro b _
  exact memLp_compact_mul_of_local (coordinateWordDerivative_contDiff hχ _).continuous
    (coordinateWordDerivative_hasCompactSupport hc _)
    (hloc _ ((maskedDirections_length_le I _).trans hr))

theorem rawCutoffJet_hasCompactSupport (J : List (Fin n) → Space n → ℝ)
    {χ : Space n → ℝ} (hc : HasCompactSupport χ) (r : ℕ) (I : Fin r → Fin n) :
    HasCompactSupport (rawCutoffJet J χ r I) := by
  exact compactSupport_finsetSum Finset.univ (fun b _ =>
    (coordinateWordDerivative_hasCompactSupport hc _).mul_right)

theorem rawCutoffJet_hasWeakCoordinateDerivative
    (J : List (Fin n) → Space n → ℝ)
    (hloc : ∀ L, L.length ≤ s → ∀ K : Set (Space n), IsCompact K →
      MemLp (J L) 2 (volume.restrict K))
    (hweak : ∀ L, L.length < s → ∀ i,
      HasLocalWeakCoordinateDerivative (J L) (J (i::L)) i)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hr : r < s) (I : Fin r → Fin n) (i : Fin n) :
    HasWeakCoordinateDerivative (rawCutoffJet J χ r I) i
      ((rawCutoffJet_memLp J hloc hχ hc (show r+1 ≤ s by omega) (Fin.cons i I)).toLp
        (rawCutoffJet J χ (r+1) (Fin.cons i I))) := by
  let A (b : Fin r → Bool) : Space n → ℝ := fun x =>
    coordinateWordDerivative χ (maskedDirections I b) x*
      J (maskedDirections I (fun j => !(b j))) x
  let D (b : Fin r → Bool) : Space n → ℝ := fun x =>
    coordinateWordDerivative χ (maskedDirections I b) x*
      J (i::maskedDirections I (fun j => !(b j))) x+
    coordinateDerivative (coordinateWordDerivative χ (maskedDirections I b)) i x*
      J (maskedDirections I (fun j => !(b j))) x
  have hA (b : Fin r → Bool) : MemLp (A b) 2 volume :=
    memLp_compact_mul_of_local (coordinateWordDerivative_contDiff hχ _).continuous
      (coordinateWordDerivative_hasCompactSupport hc _)
      (hloc _ ((maskedDirections_length_le I _).trans hr.le))
  have hD (b : Fin r → Bool) : MemLp (D b) 2 volume := by
    apply MemLp.add
    · exact memLp_compact_mul_of_local (coordinateWordDerivative_contDiff hχ _).continuous
        (coordinateWordDerivative_hasCompactSupport hc _)
        (hloc _ (by
          simp only [List.length_cons]
          have hl := maskedDirections_length_le I (fun j => !(b j))
          omega))
    · rw [←coordinateWordDerivative_cons]
      exact memLp_compact_mul_of_local (coordinateWordDerivative_contDiff hχ _).continuous
        (coordinateWordDerivative_hasCompactSupport hc _)
        (hloc _ ((maskedDirections_length_le I _).trans hr.le))
  intro ψ hψ hψc
  have hψLp : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
  have hdψLp : MemLp (coordinateDerivative ψ i) 2 volume :=
    (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_coordinateDerivative hψc i)
  have hw (b : Fin r → Bool) :
      (∫ x, A b x*coordinateDerivative ψ i x) = -(∫ x, D b x*ψ x) := by
    have hl := maskedDirections_length_le I (fun j => !(b j))
    obtain ⟨g,hg,hge⟩ := (hweak _ (hl.trans_lt hr) i).compact_mul
      (hloc _ (hl.trans hr.le))
      (hloc _ (by simp only [List.length_cons]; omega))
      ((coordinateWordDerivative_contDiff hχ _).of_le (by simp))
      (coordinateWordDerivative_hasCompactSupport hc _)
    have he := hg ψ hψ hψc
    change (∫ x, A b x*coordinateDerivative ψ i x) = -(∫ x, g x*ψ x) at he
    rw [he]
    congr 1
    apply integral_congr_ae
    filter_upwards [hge] with x hx
    rw [hx]
  calc
    _ = ∫ x, ∑ b : Fin r → Bool, A b x*coordinateDerivative ψ i x := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [rawCutoffJet,A,Finset.sum_mul]
    _ = ∑ b : Fin r → Bool, ∫ x, A b x*coordinateDerivative ψ i x :=
      integral_finsetSum Finset.univ (fun b _ => (hA b).integrable_mul hdψLp)
    _ = ∑ b : Fin r → Bool, -(∫ x, D b x*ψ x) :=
      Finset.sum_congr rfl (fun b _ => hw b)
    _ = -(∫ x, ∑ b : Fin r → Bool, D b x*ψ x) := by
      have he : (∫ x, ∑ b : Fin r → Bool, D b x*ψ x) =
          ∑ b : Fin r → Bool, ∫ x, D b x*ψ x :=
        integral_finsetSum Finset.univ (fun b _ => (hD b).integrable_mul hψLp)
      rw [he,Finset.sum_neg_distrib]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [(rawCutoffJet_memLp J hloc hχ hc (show r+1 ≤ s by omega)
        (Fin.cons i I)).coeFn_toLp] with x hx
      rw [hx,rawCutoffJet_cons]
      simp only [D,Finset.sum_mul]

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.rawCutoffJet_hasWeakCoordinateDerivative

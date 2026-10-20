import TopTensorWeakJetGluing

/-! One globally raw weak jet through the extra derivative, with all
known lower jets literally the actual weighted tensor primitives. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric TemperedDistribution
open scoped ContDiff Topology BigOperators SchwartzMap LineDeriv
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n r : ℕ} {φ : Space n → ℝ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

/-- No top global weighted L² or weak-evolution premise is assumed. -/
theorem exists_global_raw_tensor_jet
    (hφ : ContDiff ℝ 1 φ) (U : (k : ℕ) → OrderedTensorField φ k)
    (hgraph : ∀ k, k < r → ∃ V : TensorPrimitive (φ := φ) (OrderedTensorIndex n k),
      finitePrimitiveValue (OrderedTensorIndex n k) V=U k ∧
        ∀ I i, weightedH1Derivative φ i (V I)=U (k+1) (Fin.cons i I))
    (hgain : ∀ {χ : Space n → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ),
      MemSobolev ((r : ℝ)+1) 2
        (compactWeightedTempered hφ.continuous hχ.continuous hc (tensorWordLp U []))) :
    ∃ J : List (Fin n) → Space n → ℝ,
      (∀ L, L.length ≤ r → J L=(tensorWordLp U L : Space n → ℝ)) ∧
      (∀ L, L.length < r+1 → MemLp (J L) 2 (potentialMeasure φ)) ∧
      (∀ L, L.length ≤ r+1 → ∀ K : Set (Space n), IsCompact K →
        MemLp (J L) 2 (volume.restrict K)) ∧
      (∀ L, L.length ≤ r → ∀ i,
        HasLocalWeakCoordinateDerivative (J L) (J (i::L)) i) := by
  classical
  let W : List (Fin n) → Fin n → Space n → ℝ := fun L i =>
    if hL : L.length=r then
      Classical.choose (exists_local_top_tensor_weak_derivative hφ U hgraph hgain L hL i)
    else 0
  have hWloc (L : List (Fin n)) (hL : L.length=r) (i : Fin n) :
      ∀ K : Set (Space n), IsCompact K → MemLp (W L i) 2 (volume.restrict K) := by
    dsimp only [W]
    rw [dite_eq_left hL]
    exact (Classical.choose_spec
      (exists_local_top_tensor_weak_derivative hφ U hgraph hgain L hL i)).1
  have hWweak (L : List (Fin n)) (hL : L.length=r) (i : Fin n) :
      HasLocalWeakCoordinateDerivative (tensorWordLp U L) (W L i) i := by
    dsimp only [W]
    rw [dite_eq_left hL]
    exact (Classical.choose_spec
      (exists_local_top_tensor_weak_derivative hφ U hgraph hgain L hL i)).2
  let J : List (Fin n) → Space n → ℝ := fun L =>
    if L.length ≤ r then (tensorWordLp U L : Space n → ℝ) else
      match L with
      | [] => 0
      | i::M => W M i
  have hJlower (L : List (Fin n)) (hL : L.length ≤ r) :
      J L=(tensorWordLp U L : Space n → ℝ) := by
    dsimp only [J]
    rw [ite_eq_left hL]
  have hJtop (L : List (Fin n)) (hL : L.length=r) (i : Fin n) : J (i::L)=W L i := by
    dsimp only [J]
    rw [ite_eq_right (by simp only [List.length_cons,hL]; omega)]
  refine ⟨J,hJlower,?_,?_,?_⟩
  · intro L hL
    rw [hJlower L (by omega)]
    exact Lp.memLp _
  · intro L hL K hK
    by_cases hlow : L.length ≤ r
    · rw [hJlower L hlow]
      exact tensorWordLp_memLp_restrict hφ.continuous U L hK
    · cases L with
      | nil => simp at hlow
      | cons i L =>
        have hlen : L.length=r := by simp only [List.length_cons] at hL hlow; omega
        rw [hJtop L hlen i]
        exact hWloc L hlen i K hK
  · intro L hL i
    rw [hJlower L hL]
    by_cases hlt : L.length < r
    · rw [hJlower (i::L) (by simp only [List.length_cons]; omega)]
      intro ψ hψ hc
      exact tensorWordLp_weak_identity hφ U hgraph L hlt i hψ hc
    · have hlen : L.length=r := by omega
      rw [hJtop L hlen i]
      exact hWweak L hlen i

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.exists_global_raw_tensor_jet

import ClosedTensorGradientGraph

/-! Actual all-order weighted Sobolev primitives. Every derivative level is
an actual weighted L² field, and each consecutive pair is witnessed by the
existing centered weighted H¹ graph with its literal weak derivatives.
No Sobolev primitive or approximation property is an input hypothesis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ} {φ : Space n → ℝ}
variable [IsProbabilityMeasure (potentialMeasure φ)]
variable {κ : ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ),
    κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

include hκ hlower in
/-- An actual Wˢ,² primitive tower for every compatible rank-s tensor.
The fields above s are unused; all stated identities concern levels ≤s. -/
theorem exists_iterated_compatibleTensorPrimitive (s : ℕ)
    (F : CompatibleTensorHilbert (hφ.of_le (by simp)) s) :
    ∃ U : (k : ℕ) → OrderedTensorField φ k,
      U s = (F : OrderedTensorField φ s) ∧
      (∀ k, k ≤ s → U k ∈ compatibleSymmetricTensorSubspace (hφ.of_le (by simp)) k) ∧
      (∀ k, k < s → U k ∈ centeredCompatibleTensorSubspace (hφ.of_le (by simp)) k) ∧
      (∀ k, k < s → ∃ V : TensorPrimitive (φ := φ) (OrderedTensorIndex n k),
        finitePrimitiveValue (OrderedTensorIndex n k) V = U k ∧
          ∀ I i, weightedH1Derivative φ i (V I) = U (k + 1) (Fin.cons i I)) ∧
      ∀ k, k ≤ s → ‖U k‖ ≤ (Real.sqrt κ⁻¹) ^ (s - k) * ‖F‖ := by
  induction s with
  | zero =>
    let U : (k : ℕ) → OrderedTensorField φ k := fun k =>
      if hk : k = 0 then hk.symm ▸ (F : OrderedTensorField φ 0) else 0
    refine ⟨U, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [U, ↓reduceDIte]
    · intro k hk
      have he : k = 0 := by omega
      subst k
      simpa only [U, ↓reduceDIte] using F.property
    · intro k hk
      omega
    · intro k hk
      omega
    · intro k hk
      have he : k = 0 := by omega
      subst k
      simp only [U, ↓reduceDIte, Nat.sub_self, pow_zero, one_mul]
      exact le_rfl
  | succ s ih =>
    let P := compatibleTensorInverse hφ hκ hlower s F
    let Q : CompatibleTensorHilbert (hφ.of_le (by simp)) s :=
      centeredCompatibleTensorInclusion (hφ.of_le (by simp)) s P
    obtain ⟨U, htop, hmem, hcenter, hgraph, hnorm⟩ := ih Q
    let W : (k : ℕ) → OrderedTensorField φ k := fun k =>
      if hk : k = s + 1 then hk.symm ▸ (F : OrderedTensorField φ (s + 1)) else U k
    have hs : s ≠ s + 1 := by omega
    have hQ : (Q : OrderedTensorField φ s) = (P : OrderedTensorField φ s) := rfl
    have htop' : U s = (P : OrderedTensorField φ s) := htop.trans hQ
    refine ⟨W, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [W, ↓reduceDIte]
    · intro k hk
      by_cases he : k = s + 1
      · subst k
        simpa only [W, ↓reduceDIte] using F.property
      · simpa only [W, dif_neg he] using hmem k (by omega)
    · intro k hk
      have he : k ≠ s + 1 := by omega
      by_cases hks : k = s
      · subst k
        simpa only [W, dif_neg hs, htop'] using P.property
      · simpa only [W, dif_neg he] using hcenter k (by omega)
    · intro k hk
      by_cases hks : k = s
      · subst k
        refine ⟨compatibleTensorPrimitiveGraph hφ hκ hlower s F, ?_, ?_⟩
        · simp only [W, dif_neg hs, htop']
          rfl
        · intro I i
          simp only [W, ↓reduceDIte]
          exact compatibleTensorPrimitive_derivative hφ hκ hlower _ F.property I i
      · have he : k ≠ s + 1 := by omega
        have he' : k + 1 ≠ s + 1 := by omega
        simpa only [W, dif_neg he, dif_neg he'] using hgraph k (by omega)
    · intro k hk
      by_cases he : k = s + 1
      · subst k
        simp only [W, ↓reduceDIte, Nat.sub_self, pow_zero, one_mul]
        exact le_rfl
      · have hks : k ≤ s := by omega
        have hb : ‖Q‖ ≤ Real.sqrt κ⁻¹ * ‖F‖ := by
          change ‖compatibleTensorPrimitive hφ hκ hlower s (F : OrderedTensorField φ (s + 1))‖ ≤
            Real.sqrt κ⁻¹ * ‖(F : OrderedTensorField φ (s + 1))‖
          exact compatibleTensorPrimitive_norm_le hφ hκ hlower (r := s) _
        simp only [W, dif_neg he]
        calc
          ‖U k‖ ≤ (Real.sqrt κ⁻¹) ^ (s - k) * ‖Q‖ := hnorm k hks
          _ ≤ (Real.sqrt κ⁻¹) ^ (s - k) * (Real.sqrt κ⁻¹ * ‖F‖) :=
            mul_le_mul_of_nonneg_left hb (pow_nonneg (Real.sqrt_nonneg _) _)
          _ = (Real.sqrt κ⁻¹) ^ (s + 1 - k) * ‖F‖ := by
            rw [show s + 1 - k = (s - k) + 1 by omega, pow_succ]
            ring

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.exists_iterated_compatibleTensorPrimitive

import CompatibleTensorSpace

/-! Actual arbitrary-rank centered primitives. The full distributional
compatibility hypothesis is enough: componentwise Dirichlet primitives
reconstruct the field, remain symmetric and compatible, and satisfy the
same scalar bound at every rank. -/
noncomputable section
open MeasureTheory Set Matrix
open scoped ContDiff BigOperators RealInnerProductSpace ENNReal
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ),
    κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

def compatibleTensorPrimitiveGraph (r : ℕ) : OrderedTensorField φ (r + 1) →L[ℝ]
    TensorPrimitive (φ := φ) (OrderedTensorIndex n r) :=
  (finiteGradientPrimitive (hφ.of_le (by simp)) hκ hlower (OrderedTensorIndex n r)).comp
    (orderedTensorSlices r)

@[simp] lemma compatibleTensorPrimitiveGraph_apply {r : ℕ}
    (F : OrderedTensorField φ (r + 1)) (I : OrderedTensorIndex n r) :
    compatibleTensorPrimitiveGraph hφ hκ hlower r F I =
      weightedGradientPrimitive (hφ.of_le (by simp)) hκ hlower (orderedTensorSlice r I F) := rfl

def compatibleTensorPrimitive (r : ℕ) :
    OrderedTensorField φ (r + 1) →L[ℝ] OrderedTensorField φ r :=
  (finitePrimitiveValue (OrderedTensorIndex n r)).comp
    (compatibleTensorPrimitiveGraph hφ hκ hlower r)

@[simp] lemma compatibleTensorPrimitive_apply {r : ℕ}
    (F : OrderedTensorField φ (r + 1)) (I : OrderedTensorIndex n r) :
    compatibleTensorPrimitive hφ hκ hlower r F I =
      weightedH1Value φ (compatibleTensorPrimitiveGraph hφ hκ hlower r F I) := rfl

theorem compatibleTensorPrimitive_derivative {r : ℕ}
    (F : OrderedTensorField φ (r + 1))
    (hF : F ∈ compatibleSymmetricTensorSubspace (hφ.of_le (by simp)) (r + 1))
    (I : OrderedTensorIndex n r) (i : Fin n) :
    weightedH1Derivative φ i (compatibleTensorPrimitiveGraph hφ hκ hlower r F I) =
      F (Fin.cons i I) := by
  have hcurl := (mem_orderedTensorCurlSubspace_succ_iff (hφ.of_le (by simp)) F).mp hF.2 I
  have he := weightedGradientPrimitive_reconstruct_curlFree hφ hκ hlower
    (orderedTensorSlice r I F) hcurl
  exact congrArg (fun G : VectorField (φ := φ) => G i) he

theorem compatibleTensorPrimitive_symmetric {r : ℕ}
    (F : OrderedTensorField φ (r + 1))
    (hF : F ∈ orderedTensorSymmetricSubspace φ (r + 1)) :
    compatibleTensorPrimitive hφ hκ hlower r F ∈ orderedTensorSymmetricSubspace φ r := by
  rw [mem_orderedTensorSymmetricSubspace_iff]
  intro I J hIJ
  have hs : orderedTensorSlice r I F = orderedTensorSlice r J F := by
    apply PiLp.ext
    intro i
    exact tensor_symmetry_cons F hF hIJ i
  simp only [compatibleTensorPrimitive_apply, compatibleTensorPrimitiveGraph_apply, hs]

theorem compatibleTensorPrimitive_compatible {r : ℕ}
    (F : OrderedTensorField φ (r + 1))
    (hF : F ∈ compatibleSymmetricTensorSubspace (hφ.of_le (by simp)) (r + 1)) :
    compatibleTensorPrimitive hφ hκ hlower r F ∈
      orderedTensorCurlSubspace (hφ.of_le (by simp)) r := by
  cases r with
  | zero => trivial
  | succ r =>
    rw [mem_orderedTensorCurlSubspace_succ_iff]
    intro I
    rw [mem_weightedCurlFreeSubspace_iff]
    intro ψ hψ hc i j
    have hi := weightedH1_unweighted_weak_identity (hφ.of_le (by simp))
      (compatibleTensorPrimitiveGraph hφ hκ hlower (r + 1) F (Fin.cons i I))
      (hψ.of_le (by simp)) hc j
    have hj := weightedH1_unweighted_weak_identity (hφ.of_le (by simp))
      (compatibleTensorPrimitiveGraph hφ hκ hlower (r + 1) F (Fin.cons j I))
      (hψ.of_le (by simp)) hc i
    rw [compatibleTensorPrimitive_derivative hφ hκ hlower F hF] at hi hj
    rw [tensor_symmetry_swap F hF.1 I j i] at hi
    exact hi.trans hj.symm

theorem compatibleTensorPrimitive_mem {r : ℕ}
    (F : OrderedTensorField φ (r + 1))
    (hF : F ∈ compatibleSymmetricTensorSubspace (hφ.of_le (by simp)) (r + 1)) :
    compatibleTensorPrimitive hφ hκ hlower r F ∈
      compatibleSymmetricTensorSubspace (hφ.of_le (by simp)) r :=
  ⟨compatibleTensorPrimitive_symmetric hφ hκ hlower F hF.1,
    compatibleTensorPrimitive_compatible hφ hκ hlower F hF⟩

theorem compatibleTensorPrimitive_integral_eq_zero {r : ℕ}
    (F : OrderedTensorField φ (r + 1)) (I : OrderedTensorIndex n r) :
    (∫ x, compatibleTensorPrimitive hφ hκ hlower r F I x ∂potentialMeasure φ) = 0 :=
  weightedGradientPrimitive_integral_eq_zero (hφ.of_le (by simp)) hκ hlower
    (orderedTensorSlice r I F)

include hκ hlower in
/-- This uniqueness is in the actual centered graph, hence includes every
centered W¹,² primitive represented in the released faithful graph. -/
theorem existsUnique_compatibleTensorPrimitiveGraph {r : ℕ}
    (F : OrderedTensorField φ (r + 1))
    (hF : F ∈ compatibleSymmetricTensorSubspace (hφ.of_le (by simp)) (r + 1)) :
    ∃! U : TensorPrimitive (φ := φ) (OrderedTensorIndex n r),
      ∀ I i, weightedH1Derivative φ i (U I) = F (Fin.cons i I) := by
  refine ⟨compatibleTensorPrimitiveGraph hφ hκ hlower r F,
    compatibleTensorPrimitive_derivative hφ hκ hlower F hF, ?_⟩
  intro U hU
  apply PiLp.ext
  intro I
  have he : weightedH1Gradient φ (U I) = orderedTensorSlice r I F := by
    apply PiLp.ext
    intro i
    exact hU I i
  have hp := congrArg (weightedGradientPrimitive (hφ.of_le (by simp)) hκ hlower) he
  simpa only [weightedGradientPrimitive_gradient, compatibleTensorPrimitiveGraph_apply] using hp

theorem compatibleTensorPrimitive_norm_le {r : ℕ} (F : OrderedTensorField φ (r + 1)) :
    ‖compatibleTensorPrimitive hφ hκ hlower r F‖ ≤ Real.sqrt κ⁻¹ * ‖F‖ := by
  have he := finiteGradientPrimitive_value_norm_le (hφ.of_le (by simp)) hκ hlower
    (orderedTensorSlices r F)
  simpa only [compatibleTensorPrimitive, compatibleTensorPrimitiveGraph,
    ContinuousLinearMap.comp_apply, orderedTensorSlices_norm] using he

theorem compatibleTensorPrimitive_norm_le_of_scalar_bound {C : ℝ}
    (hC : 0 ≤ C)
    (hbound : ∀ G : VectorField (φ := φ),
      ‖weightedH1Value φ (weightedGradientPrimitive (hφ.of_le (by simp)) hκ hlower G)‖ ≤
        C * ‖G‖)
    {r : ℕ} (F : OrderedTensorField φ (r + 1)) :
    ‖compatibleTensorPrimitive hφ hκ hlower r F‖ ≤ C * ‖F‖ := by
  have hs : (∑ I : OrderedTensorIndex n r,
      ‖weightedH1Value φ (weightedGradientPrimitive (hφ.of_le (by simp)) hκ hlower
        (orderedTensorSlice r I F))‖ ^ 2) ≤
        ∑ I : OrderedTensorIndex n r, (C * ‖orderedTensorSlice r I F‖) ^ 2 := by
    apply Finset.sum_le_sum
    intro I _
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mpr (hbound _)
  have hl : ‖compatibleTensorPrimitive hφ hκ hlower r F‖ ^ 2 =
      ∑ I : OrderedTensorIndex n r,
        ‖weightedH1Value φ (weightedGradientPrimitive (hφ.of_le (by simp)) hκ hlower
          (orderedTensorSlice r I F))‖ ^ 2 := by
    simp only [PiLp.norm_sq_eq_of_L2, compatibleTensorPrimitive_apply,
      compatibleTensorPrimitiveGraph_apply]
  have hr : (∑ I : OrderedTensorIndex n r, (C * ‖orderedTensorSlice r I F‖) ^ 2) =
      (C * ‖F‖) ^ 2 := by
    simp only [mul_pow, ← Finset.mul_sum]
    have hnorm := orderedTensorSlices_norm_sq F
    rw [PiLp.norm_sq_eq_of_L2] at hnorm
    rw [← hnorm]
    rfl
  rw [← hl, hr] at hs
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp hs

/-- A single actual attained scalar eigenvalue controls every tensor rank.
No universal numerical bound is a premise or a conclusion here. -/
theorem exists_optimal_compatibleTensorPrimitive_bound (hn : 0 < n) :
    ∃ lam : ℝ, 0 < lam ∧
      poincareConstant (potentialMeasure φ) = ENNReal.ofReal lam⁻¹ ∧
      ∀ (r : ℕ) (F : OrderedTensorField φ (r + 1)),
        ‖compatibleTensorPrimitive hφ hκ hlower r F‖ ≤ Real.sqrt lam⁻¹ * ‖F‖ := by
  obtain ⟨lam, hlam, hCP, hb⟩ := exists_optimal_weightedGradientPrimitive_bound
    (hφ.of_le (by simp)) hκ hlower hn
  exact ⟨lam, hlam, hCP, fun _ F =>
    compatibleTensorPrimitive_norm_le_of_scalar_bound hφ hκ hlower (Real.sqrt_nonneg _) hb F⟩

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.compatibleTensorPrimitive_derivative
#print axioms KLS.DeterministicBridgeIntegration.compatibleTensorPrimitive_mem
#print axioms KLS.DeterministicBridgeIntegration.existsUnique_compatibleTensorPrimitiveGraph
#print axioms KLS.DeterministicBridgeIntegration.exists_optimal_compatibleTensorPrimitive_bound

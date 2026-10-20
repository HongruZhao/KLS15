import CompactPotentialTensorDensity
import ClosedTensorGradientGraph

/-! The actual compact-potential core of the compatible tensor gradient.
The approximation is in both the value and the literal weak gradient.
This does not identify a core for the adjoint projected divergence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n r : ℕ} {φ ψ : Space n → ℝ}
variable [IsProbabilityMeasure (potentialMeasure φ)]
variable {κ : ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ),
    κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

/-- The primitive of an actual compact potential tensor is its actual
preceding derivative tensor with the coordinatewise means removed. -/
theorem compatibleTensorPrimitive_compactPotential
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (r : ℕ) :
    compatibleTensorPrimitive hφ hκ hlower r
      (compactPotentialTensorLp hφ.continuous hψ hc (r + 1)) =
        orderedTensorCenter φ r (compactPotentialTensorLp hφ.continuous hψ hc r) := by
  apply PiLp.ext
  intro I
  obtain ⟨V, hv, hd⟩ := exists_weightedH1_of_smoothCompact hφ.continuous
    ((coordinatePotentialTensor_contDiff hψ r I).of_le (by simp))
    (coordinatePotentialTensor_hasCompactSupport hc r I)
  have hgrad : weightedH1Gradient φ V = orderedTensorSlice r I
      (compactPotentialTensorLp hφ.continuous hψ hc (r + 1)) := by
    apply PiLp.ext
    intro i
    apply Lp.ext
    filter_upwards [hd i, compactTensorLp_ae hφ.continuous
      (coordinatePotentialTensor ψ (r + 1))
      (fun J => (coordinatePotentialTensor_contDiff hψ (r + 1) J).continuous)
      (coordinatePotentialTensor_hasCompactSupport hc (r + 1)) (Fin.cons i I)] with x hx hy
    exact hx.trans (hy.trans (congrFun (coordinatePotentialTensor_cons ψ I i) x)).symm
  have hinv := congrArg (weightedGradientPrimitive (hφ.of_le (by simp)) hκ hlower) hgrad
  rw [weightedGradientPrimitive_gradient] at hinv
  rw [compatibleTensorPrimitive_apply, compatibleTensorPrimitiveGraph_apply, ← hinv,
    orderedTensorCenter_apply]
  apply Lp.ext
  have hF : (compactPotentialTensorLp hφ.continuous hψ hc r I : Space n → ℝ)
      =ᵐ[potentialMeasure φ] coordinatePotentialTensor ψ r I :=
    compactTensorLp_ae hφ.continuous (coordinatePotentialTensor ψ r)
    (fun J => (coordinatePotentialTensor_contDiff hψ r J).continuous)
    (coordinatePotentialTensor_hasCompactSupport hc r) I
  have hi := integral_congr_ae hF
  filter_upwards [hv, CenteredL2.center_ae (potentialMeasure φ)
    (compactPotentialTensorLp hφ.continuous hψ hc r I), hF] with x hx hy hz
  exact hx.trans (by simpa only [hz, hi] using hy.symm)

def compactPotentialGradientPairSet (hφ : Continuous φ) (r : ℕ) :
    Set (OrderedTensorField φ r × OrderedTensorField φ (r + 1)) :=
  {p | ∃ (ψ : Space n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ),
    p = (orderedTensorCenter φ r (compactPotentialTensorLp hφ hψ hc r),
      compactPotentialTensorLp hφ hψ hc (r + 1))}

include hκ hlower in
/-- A genuine graph-core equality in the ambient product Hilbert space:
every literal compatible gradient pair is a joint L² limit of centered
compact potential tensors and their actual next derivatives. -/
theorem closure_compactPotentialGradientPairSet_eq_graph (r : ℕ) :
    closure (compactPotentialGradientPairSet hφ.continuous r) =
      {p | p.2 ∈ compatibleSymmetricTensorSubspace (hφ.of_le (by simp)) (r + 1) ∧
        p.1 = compatibleTensorPrimitive hφ hκ hlower r p.2} := by
  have hc : IsClosed {p : OrderedTensorField φ r × OrderedTensorField φ (r + 1) |
      p.2 ∈ compatibleSymmetricTensorSubspace (hφ.of_le (by simp)) (r + 1) ∧
        p.1 = compatibleTensorPrimitive hφ hκ hlower r p.2} :=
    ((compatibleSymmetricTensorSubspace_isClosed (hφ.of_le (by simp)) (r + 1)).preimage
      continuous_snd).inter (isClosed_eq continuous_fst
        ((compatibleTensorPrimitive hφ hκ hlower r).continuous.comp continuous_snd))
  apply subset_antisymm
  · apply hc.closure_subset_iff.mpr
    rintro p ⟨ψ, hψ, hψc, rfl⟩
    exact ⟨compactPotentialTensorLp_mem (hφ.of_le (by simp)) hψ hψc (r + 1),
      (compatibleTensorPrimitive_compactPotential hφ hκ hlower hψ hψc r).symm⟩
  · rintro ⟨U, F⟩ ⟨hF, hU⟩
    let T : OrderedTensorField φ (r + 1) →
        OrderedTensorField φ r × OrderedTensorField φ (r + 1) :=
      fun H => (compatibleTensorPrimitive hφ hκ hlower r H, H)
    have hT : Continuous T := (compatibleTensorPrimitive hφ hκ hlower r).continuous.prodMk continuous_id
    have hpre : IsClosed (T ⁻¹' closure (compactPotentialGradientPairSet hφ.continuous r)) :=
      isClosed_closure.preimage hT
    have hsub : compactPotentialTensorSet hφ.continuous (r + 1) ⊆
        T ⁻¹' closure (compactPotentialGradientPairSet hφ.continuous r) := by
      rintro H ⟨ψ, hψ, hψc, rfl⟩
      apply subset_closure
      refine ⟨ψ, hψ, hψc, ?_⟩
      simp only [T, compatibleTensorPrimitive_compactPotential hφ hκ hlower hψ hψc r]
    have hmem := hpre.closure_subset_iff.mpr hsub
    rw [closure_compactPotentialTensorSet_eq_compatible hφ hκ hlower] at hmem
    have he := hmem hF
    change (compatibleTensorPrimitive hφ hκ hlower r F, F) ∈
      closure (compactPotentialGradientPairSet hφ.continuous r) at he
    change U = compatibleTensorPrimitive hφ hκ hlower r F at hU
    rw [hU]
    exact he

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.compatibleTensorPrimitive_compactPotential
#print axioms KLS.DeterministicBridgeIntegration.closure_compactPotentialGradientPairSet_eq_graph

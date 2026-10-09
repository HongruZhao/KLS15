import TensorInverseAdjointCore

/-! The actual closed tensor gradient graph. Membership requires literal
centered weighted H¹ representatives and all their distributional first
derivatives. The bounded primitive identifies this graph exactly; no
density or compact-core property is assumed or concluded. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace
namespace KLS.DeterministicBridgeIntegration
variable {n r : ℕ} {φ : Space n → ℝ}
variable [IsProbabilityMeasure (potentialMeasure φ)]

def CompatibleTensorGradientGraph (hφ : ContDiff ℝ 1 φ)
    (U : CenteredCompatibleTensorHilbert hφ r)
    (F : CompatibleTensorHilbert hφ (r + 1)) : Prop :=
  ∃ V : TensorPrimitive (φ := φ) (OrderedTensorIndex n r),
    finitePrimitiveValue (OrderedTensorIndex n r) V = (U : OrderedTensorField φ r) ∧
      ∀ I i, weightedH1Derivative φ i (V I) = F.val (Fin.cons i I)

variable {κ : ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ),
    κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

theorem compatibleTensorGradientGraph_iff
    (U : CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) r)
    (F : CompatibleTensorHilbert (hφ.of_le (by simp)) (r + 1)) :
    CompatibleTensorGradientGraph (hφ.of_le (by simp)) U F ↔
      U = compatibleTensorInverse hφ hκ hlower r F := by
  constructor
  · rintro ⟨V, hV, hd⟩
    obtain ⟨W, hW, hu⟩ := existsUnique_compatibleTensorPrimitiveGraph hφ hκ hlower
      (F : OrderedTensorField φ (r + 1)) F.property
    have hVW : V = compatibleTensorPrimitiveGraph hφ hκ hlower r F :=
      (hu V hd).trans (hu _ (compatibleTensorPrimitive_derivative hφ hκ hlower _ F.property)).symm
    apply Subtype.ext
    exact hV.symm.trans (congrArg (finitePrimitiveValue (OrderedTensorIndex n r)) hVW)
  · intro he
    refine ⟨compatibleTensorPrimitiveGraph hφ hκ hlower r F, ?_,
      compatibleTensorPrimitive_derivative hφ hκ hlower _ F.property⟩
    exact (congrArg (fun V : CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) r =>
      (V : OrderedTensorField φ r)) he).symm

theorem compatibleTensorInverse_injective :
    Function.Injective (compatibleTensorInverse hφ hκ hlower r) := by
  intro F H he
  apply Subtype.ext
  apply PiLp.ext
  intro I
  have hv := congrArg (fun V : CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) r =>
    (V : OrderedTensorField φ r) (Fin.tail I)) he
  have hg : compatibleTensorPrimitiveGraph hφ hκ hlower r F (Fin.tail I) =
      compatibleTensorPrimitiveGraph hφ hκ hlower r H (Fin.tail I) :=
    weightedH1Value_injective (hφ.of_le (by simp)) hv
  have hd := congrArg (weightedH1Derivative φ (I 0)) hg
  rw [compatibleTensorPrimitive_derivative hφ hκ hlower _ F.property,
    compatibleTensorPrimitive_derivative hφ hκ hlower _ H.property,
    Fin.cons_self_tail] at hd
  exact hd

include hκ hlower in
theorem compatibleTensorGradientGraph_isClosed :
    IsClosed {p : CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) r ×
      CompatibleTensorHilbert (hφ.of_le (by simp)) (r + 1) |
      CompatibleTensorGradientGraph (hφ.of_le (by simp)) p.1 p.2} := by
  have hc := isClosed_eq continuous_fst
    ((compatibleTensorInverse hφ hκ hlower r).continuous.comp continuous_snd)
  convert hc using 1
  ext p
  exact compatibleTensorGradientGraph_iff hφ hκ hlower p.1 p.2

include hκ hlower in
theorem compatibleTensorGradientGraph_derivative_unique
    (U : CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) r)
    (F H : CompatibleTensorHilbert (hφ.of_le (by simp)) (r + 1))
    (hF : CompatibleTensorGradientGraph (hφ.of_le (by simp)) U F)
    (hH : CompatibleTensorGradientGraph (hφ.of_le (by simp)) U H) : F = H := by
  apply compatibleTensorInverse_injective hφ hκ hlower
  exact ((compatibleTensorGradientGraph_iff hφ hκ hlower U F).mp hF).symm.trans
    ((compatibleTensorGradientGraph_iff hφ hκ hlower U H).mp hH)

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.compatibleTensorGradientGraph_iff
#print axioms KLS.DeterministicBridgeIntegration.compatibleTensorInverse_injective
#print axioms KLS.DeterministicBridgeIntegration.compatibleTensorGradientGraph_isClosed

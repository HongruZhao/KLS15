import CenteredProjectedDivergence

/-! The literal compact divergence is an actual adjoint inverse core:
J̃ᵣ* Sᵣ F = F. All spaces and maps are the previously constructed
distributional tensor spaces and centered weighted gradient primitives. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace
namespace KLS.DeterministicBridgeIntegration
variable {n r : ℕ} {φ : Space n → ℝ}

lemma orderedTensor_inner_cons (H F : OrderedTensorField φ (r + 1)) :
    inner ℝ H F = ∑ I : OrderedTensorIndex n r, ∑ j,
      inner ℝ (H (Fin.cons j I)) (F (Fin.cons j I)) := by
  rw [PiLp.inner_apply, Finset.sum_comm]
  symm
  calc
    _ = ∑ p : Fin n × OrderedTensorIndex n r,
        inner ℝ (H (Fin.cons p.1 p.2)) (F (Fin.cons p.1 p.2)) :=
      (Fintype.sum_prod_type _).symm
    _ = _ := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (r + 1) => Fin n))
      _ _ (fun _ => rfl)

variable [IsProbabilityMeasure (potentialMeasure φ)]
variable {κ : ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ),
    κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

def compactCompatibleTensor
    {F : OrderedTensorIndex n (r + 1) → Space n → ℝ}
    (hF : ∀ I, ContDiff ℝ 2 (F I)) (hc : ∀ I, HasCompactSupport (F I))
    (hsym : classicalTensorSymmetric F) (hcomp : classicalTensorCompatible F) :
    CompatibleTensorHilbert (hφ.of_le (by simp)) (r + 1) :=
  ⟨compactTensorLp hφ.continuous F (fun I => (hF I).continuous) hc,
    compactTensorLp_mem_compatible _ _ _ _ hsym hcomp⟩

def compactCenteredProjectedDivergence
    {F : OrderedTensorIndex n (r + 1) → Space n → ℝ}
    (hF : ∀ I, ContDiff ℝ 2 (F I)) (hc : ∀ I, HasCompactSupport (F I)) :
    CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) r :=
  ⟨projectedTensorDivergence (hφ.of_le (by simp)) hF hc,
    projectedTensorDivergence_mem_centered _ _ _⟩

theorem compatibleTensorInverse_compact_divergence_pairing
    {F : OrderedTensorIndex n (r + 1) → Space n → ℝ}
    (hF : ∀ I, ContDiff ℝ 2 (F I)) (hc : ∀ I, HasCompactSupport (F I))
    (hsym : classicalTensorSymmetric F) (hcomp : classicalTensorCompatible F)
    (H : CompatibleTensorHilbert (hφ.of_le (by simp)) (r + 1)) :
    inner ℝ (compatibleTensorInverse hφ hκ hlower r H)
      (compactCenteredProjectedDivergence hφ hF hc) =
      inner ℝ H (compactCompatibleTensor hφ hF hc hsym hcomp) := by
  have he := projectedTensorDivergence_graph_pairing (hφ.of_le (by simp)) hF hc
    (compatibleTensorPrimitiveGraph hφ hκ hlower r H)
    (compatibleTensorPrimitive_mem hφ hκ hlower (H : OrderedTensorField φ (r + 1)) H.property)
  change inner ℝ (compatibleTensorPrimitive hφ hκ hlower r H)
    (projectedTensorDivergence (hφ.of_le (by simp)) hF hc) = _ at he
  change inner ℝ (compatibleTensorPrimitive hφ hκ hlower r H)
    (projectedTensorDivergence (hφ.of_le (by simp)) hF hc) =
      inner ℝ (H : OrderedTensorField φ (r + 1))
        (compactTensorLp hφ.continuous F (fun I => (hF I).continuous) hc)
  rw [he, orderedTensor_inner_cons]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro j _
  rw [compatibleTensorPrimitive_derivative hφ hκ hlower _ H.property, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [compactTensorLp_ae hφ.continuous F (fun I => (hF I).continuous) hc
    (Fin.cons j I)] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial]
  ring

/-- Exact adjoint identity on literal compact compatible tensors. This does
not assert that the compact projected-divergence image is dense in Gᵣ. -/
theorem compatibleTensorInverse_adjoint_compact_divergence
    {F : OrderedTensorIndex n (r + 1) → Space n → ℝ}
    (hF : ∀ I, ContDiff ℝ 2 (F I)) (hc : ∀ I, HasCompactSupport (F I))
    (hsym : classicalTensorSymmetric F) (hcomp : classicalTensorCompatible F) :
    (compatibleTensorInverse hφ hκ hlower r).adjoint
      (compactCenteredProjectedDivergence hφ hF hc) =
        compactCompatibleTensor hφ hF hc hsym hcomp := by
  apply ext_inner_left ℝ
  intro H
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact compatibleTensorInverse_compact_divergence_pairing hφ hκ hlower hF hc hsym hcomp H

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.compatibleTensorInverse_compact_divergence_pairing
#print axioms KLS.DeterministicBridgeIntegration.compatibleTensorInverse_adjoint_compact_divergence

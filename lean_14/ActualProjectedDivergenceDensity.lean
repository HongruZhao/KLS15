import ActualOrthogonalGlobalRawJet
import RawJetCaccioppoliZero
import OrthogonalTensorTopWeakForm
import CompactPotentialDivergenceRange

/-! Genuine density of the actual projected divergence image of compact
smooth potentials. Orthogonality alone now supplies the local elliptic
regularity, weak jet, powered-cutoff tests, Fatou and centered-zero steps. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff Topology BigOperators RealInnerProductSpace
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration
variable {n r : ℕ} {φ : Space n → ℝ}
variable [IsProbabilityMeasure (potentialMeasure φ)]
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem orthogonal_compactPotentialDivergence_eq_zero
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (F : CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) r)
    (horth : ∀ (ψ : Space n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
      (hc : HasCompactSupport ψ), inner ℝ F (compactPotentialDivergenceHilbert hφ hψ hc r)=0) : F=0 := by
  obtain ⟨U,J,htop,hJ,hglobal,hlocal,hweak⟩ :=
    exists_orthogonal_tensor_global_raw_jet hφ hκ hlower F horth
  have hlink (I : OrderedTensorIndex n r) : J (List.ofFn I)=(F.val I : Space n → ℝ) := by
    rw [hJ (List.ofFn I) (by simp)]
    have he : tensorWordLp U (List.ofFn I)=F.val I := by
      rw [tensorWordLp_ofFn,htop]
    rw [he]
  have hsmooth (ψ : Space n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
      (hc : HasCompactSupport ψ) :
      (∑ I : Fin (r+1) → Fin n, ∫ x, J (List.ofFn I) x*
        coordinatePotentialTensor ψ (r+1) I x ∂potentialMeasure φ)=0 := by
    apply orthogonal_tensor_top_weak_form hφ F horth J
      (fun I => Filter.Eventually.of_forall (fun x => congrFun (hlink I) x))
      (fun I i => hweak (List.ofFn I) (by simp) i) hψ hc
  apply Subtype.ext
  exact centeredTensor_eq_zero_of_raw_jet_smooth_tests (hφ.of_le (by simp)) F.val
    F.property J hlink hglobal hlocal (fun L hL => hweak L (by omega)) hsmooth

theorem actual_compactPotentialDivergence_dense
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a)) (r : ℕ) :
    Dense {u : CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) r |
      ∃ (ψ : Space n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ),
        u=compactPotentialDivergenceHilbert hφ hψ hc r} := by
  have hd := dense_compactPotentialDivergenceRange (hφ.of_le (by simp)) r
    (fun F horth => orthogonal_compactPotentialDivergence_eq_zero hφ hκ hlower F
      (fun ψ hψ hc => horth ⟨ψ,hψ,hc⟩))
  have he : Set.range (compactPotentialDivergenceFromTest (hφ.of_le (by simp)) r)=
      {u : CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) r |
        ∃ (ψ : Space n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ),
          u=compactPotentialDivergenceHilbert hφ hψ hc r} := by
    ext u
    constructor
    · rintro ⟨ψ,rfl⟩
      exact ⟨ψ,ψ.property.1,ψ.property.2,rfl⟩
    · rintro ⟨ψ,hψ,hc,rfl⟩
      exact ⟨⟨ψ,hψ,hc⟩,rfl⟩
  rw [he] at hd
  exact hd

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.orthogonal_compactPotentialDivergence_eq_zero
#print axioms KLS.DeterministicBridgeNext.actual_compactPotentialDivergence_dense

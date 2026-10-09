import ActualOrthogonalTensorLocalGain
import GlobalRawTensorJet

/-! Literal compact-potential orthogonality supplies the actual globally
raw extra weak derivative tower. No local regularity premise remains. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Matrix TemperedDistribution
open scoped ContDiff Topology BigOperators SchwartzMap LineDeriv RealInnerProductSpace
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext
variable {n r : ℕ} {φ : Space n → ℝ}
variable [IsProbabilityMeasure (potentialMeasure φ)]
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

 theorem exists_orthogonal_tensor_global_raw_jet
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (F : CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) r)
    (horth : ∀ (ψ : Space n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
      (hc : HasCompactSupport ψ), inner ℝ F
        (KLS.DeterministicBridgeNext.compactPotentialDivergenceHilbert hφ hψ hc r)=0) :
    ∃ (U : (k : ℕ) → OrderedTensorField φ k) (J : List (Fin n) → Space n → ℝ),
      U r=F.val ∧
      (∀ L, L.length ≤ r → J L=(tensorWordLp U L : Space n → ℝ)) ∧
      (∀ L, L.length < r+1 → MemLp (J L) 2 (potentialMeasure φ)) ∧
      (∀ L, L.length ≤ r+1 → ∀ K : Set (Space n), IsCompact K →
        MemLp (J L) 2 (volume.restrict K)) ∧
      (∀ L, L.length ≤ r → ∀ i,
        HasLocalWeakCoordinateDerivative (J L) (J (i::L)) i) := by
  obtain ⟨U,htop,_,hgraph,hgain⟩ :=
    exists_orthogonal_tensor_primitive_local_gain hφ hκ hlower F horth
  have hg : ∀ {χ : Space n → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ),
      MemSobolev ((r : ℝ)+1) 2
        (compactWeightedTempered hφ.continuous hχ.continuous hc (tensorWordLp U [])) := by
    intro χ hχ hc
    simpa only [Nat.cast_add,Nat.cast_one] using hgain χ hχ hc
  obtain ⟨J,hJ,hglobal,hlocal,hweak⟩ :=
    exists_global_raw_tensor_jet (hφ.of_le (by simp)) U hgraph hg
  exact ⟨U,J,htop,hJ,hglobal,hlocal,hweak⟩

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.exists_orthogonal_tensor_global_raw_jet

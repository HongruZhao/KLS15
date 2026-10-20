import CenteredTensorZero
import RawWeakJetTestExtension

/-! Exact assembly of actual smooth orthogonality, compact Sobolev test
extension, powered cutoff Caccioppoli, Fatou, and centering. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff Topology BigOperators RealInnerProductSpace
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n r : ℕ} {φ : Space n → ℝ}
variable [IsProbabilityMeasure (potentialMeasure φ)]
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

/-- The only orthogonality input is the literal compact smooth qth-jet
weak form. All subsequent limiting and centered-zero steps are internal. -/
theorem centeredTensor_eq_zero_of_raw_jet_smooth_tests
    (hφ : ContDiff ℝ 1 φ) (U : OrderedTensorField φ r)
    (hU : U ∈ centeredCompatibleTensorSubspace hφ r)
    (J : List (Fin n) → Space n → ℝ)
    (hlink : ∀ I : OrderedTensorIndex n r,
      J (List.ofFn I)=(U I : Space n → ℝ))
    (hglobal : ∀ L, L.length < r+1 → MemLp (J L) 2 (potentialMeasure φ))
    (hlocal : ∀ L, L.length ≤ r+1 → ∀ K : Set (Space n), IsCompact K →
      MemLp (J L) 2 (volume.restrict K))
    (hweak : ∀ L, L.length < r+1 → ∀ i,
      HasLocalWeakCoordinateDerivative (J L) (J (i::L)) i)
    (hsmooth : ∀ (ψ : Space n → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∑ I : Fin (r+1) → Fin n, ∫ x,
        J (List.ofFn I) x*coordinatePotentialTensor ψ (r+1) I x ∂potentialMeasure φ)=0) : U=0 := by
  have htest (k : ℕ) := poweredCutoff_high_order_test_extension hφ.continuous J hlocal hweak hsmooth
    (by omega : r+1 ≠ 0) k
  have hzero := poweredCutoff_top_ae_zero_of_local_volume hφ.continuous
    (by omega : r+1 ≠ 0) J hglobal
    (fun I => hlocal (List.ofFn I) (by simp)) htest
  apply centeredTensor_eq_zero_of_weak_top_ae_zero hφ U hU
    (fun I i => J (i::List.ofFn I))
  · intro I i ψ hψ hc
    have hw := hweak (List.ofFn I) (by simp) i ψ hψ hc
    rw [hlink I] at hw
    exact hw
  · intro I i
    simpa only [List.ofFn_cons] using hzero (Fin.cons i I)

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.centeredTensor_eq_zero_of_raw_jet_smooth_tests

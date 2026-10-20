import RawWeakJetCutoff
import MollifiedTensorPotential

/-! Compact smooth approximants for a local raw jet tower, including the
highest derivative in the actual weighted L2 norm. -/
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n s : ℕ} {φ χ : Space n → ℝ}
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def rawMollifiedCutoffPotential (J : List (Fin n) → Space n → ℝ)
    (χ : Space n → ℝ) (k : ℕ) : Space n → ℝ :=
  mollify k (rawCutoffJet J χ 0 (fun j => Fin.elim0 j))

theorem rawMollifiedCutoffPotential_contDiff
    (J : List (Fin n) → Space n → ℝ)
    (hloc : ∀ L, L.length ≤ s → ∀ K : Set (Space n), IsCompact K →
      MemLp (J L) 2 (volume.restrict K))
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (rawMollifiedCutoffPotential J χ k) :=
  mollify_contDiff ((rawCutoffJet_memLp J hloc hχ hc (Nat.zero_le _) _).locallyIntegrable (by norm_num)) k

theorem rawMollifiedCutoffPotential_hasCompactSupport
    (J : List (Fin n) → Space n → ℝ) (hc : HasCompactSupport χ) (k : ℕ) :
    HasCompactSupport (rawMollifiedCutoffPotential J χ k) :=
  hasCompactSupport_mollify (rawCutoffJet_hasCompactSupport J hc 0 _) k

theorem coordinatePotentialTensor_rawMollifiedCutoffPotential
    (J : List (Fin n) → Space n → ℝ)
    (hloc : ∀ L, L.length ≤ s → ∀ K : Set (Space n), IsCompact K →
      MemLp (J L) 2 (volume.restrict K))
    (hweak : ∀ L, L.length < s → ∀ i,
      HasLocalWeakCoordinateDerivative (J L) (J (i::L)) i)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (r : ℕ) (hr : r ≤ s) (I : Fin r → Fin n) (k : ℕ) :
    coordinatePotentialTensor (rawMollifiedCutoffPotential J χ k) r I =
      mollify k (rawCutoffJet J χ r I) := by
  induction r with
  | zero =>
    have he : I=(fun j => Fin.elim0 j) := Subsingleton.elim _ _
    rw [he]
    rfl
  | succ r ih =>
    rw [←Fin.cons_self_tail I,coordinatePotentialTensor_cons,ih (by omega)]
    have hw := rawCutoffJet_hasWeakCoordinateDerivative J hloc hweak hχ hc
      (show r < s by omega) (Fin.tail I) (I 0)
    rw [hw.mollify_eq (rawCutoffJet_memLp J hloc hχ hc (show r ≤ s by omega)
      (Fin.tail I)) k]
    exact mollify_congr_ae (rawCutoffJet_memLp J hloc hχ hc (show r+1 ≤ s by omega)
      (Fin.cons (I 0) (Fin.tail I))).coeFn_toLp k

theorem eLpNorm_mollify_rawCutoffJet_potential_tendsto_zero
    (hφ : Continuous φ) (J : List (Fin n) → Space n → ℝ)
    (hloc : ∀ L, L.length ≤ s → ∀ K : Set (Space n), IsCompact K →
      MemLp (J L) 2 (volume.restrict K))
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (r : ℕ) (hr : r ≤ s) (I : Fin r → Fin n) :
    Tendsto (fun k => eLpNorm
      (mollify k (rawCutoffJet J χ r I)-rawCutoffJet J χ r I)
      2 (potentialMeasure φ)) atTop (𝓝 0) := by
  have hV := rawCutoffJet_memLp J hloc hχ hc hr I
  have hC := rawCutoffJet_hasCompactSupport J hc r I
  apply eLpNorm_potentialMeasure_sub_tendsto_zero_of_compact_support hφ
    (isCompact_mollifierEnlargement hC) (tsupport_mollify_subset hC)
    (subset_mollifierEnlargement _) (fun k => memLp_mollify hV k) hV
  · intro k
    exact memLp_of_continuous_hasCompactSupport hφ
      (mollify_contDiff (hV.locallyIntegrable (by norm_num)) k).continuous
      (hasCompactSupport_mollify hC k)
  · exact memLp_potentialMeasure_of_memLp_volume_compact hφ hV hC
  · exact eLpNorm_mollify_sub_tendsto_zero hV

theorem rawCutoff_classicalJet_weighted_approximation
    (hφ : Continuous φ) (J : List (Fin n) → Space n → ℝ)
    (hloc : ∀ L, L.length ≤ s → ∀ K : Set (Space n), IsCompact K →
      MemLp (J L) 2 (volume.restrict K))
    (hweak : ∀ L, L.length < s → ∀ i,
      HasLocalWeakCoordinateDerivative (J L) (J (i::L)) i)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (r : ℕ) (hr : r ≤ s) (I : Fin r → Fin n) :
    Tendsto (fun k => eLpNorm
      (coordinatePotentialTensor (rawMollifiedCutoffPotential J χ k) r I-rawCutoffJet J χ r I)
      2 (potentialMeasure φ)) atTop (𝓝 0) := by
  simp_rw [coordinatePotentialTensor_rawMollifiedCutoffPotential J hloc hweak hχ hc r hr I]
  exact eLpNorm_mollify_rawCutoffJet_potential_tendsto_zero hφ J hloc hχ hc r hr I

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.rawCutoff_classicalJet_weighted_approximation

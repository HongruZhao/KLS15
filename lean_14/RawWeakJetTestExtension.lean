import RawWeakJetMollification
import PoweredTensorCutoffRemainder

/-! Smooth compact q-th order tests extend to the actual powered cutoff
potential by local L2 pairing limits. No global L2 bound on the flux is used. -/
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS
variable {n q : ℕ} {φ χ : Space n → ℝ}
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem tendsto_integral_mul_of_L2_convergence {μ : Measure (Space n)}
    {f : ℕ → Space n → ℝ} {u b : Space n → ℝ}
    (hf : ∀ k, MemLp (f k) 2 μ) (hu : MemLp u 2 μ) (hb : MemLp b 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (f k-u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, b x*f k x ∂μ) atTop (𝓝 (∫ x, b x*u x ∂μ)) := by
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u hu).mpr hconv
  have hcont : Continuous (fun v : Lp ℝ 2 μ => inner ℝ (hb.toLp b) v) :=
    continuous_const.inner continuous_id
  have hi := hcont.continuousAt.tendsto.comp ht
  convert hi using 1
  · funext k
    dsimp only [Function.comp_def]
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hb.coeFn_toLp,(hf k).coeFn_toLp] with x hx hy
    simp [hx,hy,mul_comm]
  · rw [L2.inner_def]
    congr 1
    apply integral_congr_ae
    filter_upwards [hb.coeFn_toLp,hu.coeFn_toLp] with x hx hy
    simp [hx,hy,mul_comm]

theorem local_weighted_pairing_mollify
    (hφ : Continuous φ) {g A : Space n → ℝ} (hg : MemLp g 2 volume)
    (hc : HasCompactSupport g)
    (hA : ∀ K : Set (Space n), IsCompact K → MemLp A 2 (volume.restrict K)) :
    Tendsto (fun k => ∫ x, A x*mollify k g x ∂potentialMeasure φ) atTop
      (𝓝 (∫ x, A x*g x ∂potentialMeasure φ)) := by
  let K := mollifierEnlargement (tsupport g)
  have hK : IsCompact K := isCompact_mollifierEnlargement hc
  obtain ⟨β,hβ,hβc,hβone⟩ := exists_smooth_compact_one_on_compact hK
  have hB := memLp_compact_mul_local_potential hφ hβ.continuous hβc hA
  have hgm (k : ℕ) : MemLp (mollify k g) 2 (potentialMeasure φ) :=
    memLp_of_continuous_hasCompactSupport hφ
      (mollify_contDiff (hg.locallyIntegrable (by norm_num)) k).continuous
      (hasCompactSupport_mollify hc k)
  have hgw := memLp_potentialMeasure_of_memLp_volume_compact hφ hg hc
  have ht : Tendsto (fun k => eLpNorm (mollify k g-g) 2 (potentialMeasure φ))
      atTop (𝓝 0) := by
    apply eLpNorm_potentialMeasure_sub_tendsto_zero_of_compact_support hφ hK
      (tsupport_mollify_subset hc) (subset_mollifierEnlargement _)
      (fun k => memLp_mollify hg k) hg hgm hgw
    exact eLpNorm_mollify_sub_tendsto_zero hg
  have hp := tendsto_integral_mul_of_L2_convergence hgm hgw hB ht
  have he (f : Space n → ℝ) (hs : tsupport f ⊆ K) :
      (∫ x, (β x*A x)*f x ∂potentialMeasure φ) =
      ∫ x, A x*f x ∂potentialMeasure φ := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ tsupport f
    · rw [hβone x (hs hx),one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx,mul_zero,mul_zero]
  simpa only [he _ (tsupport_mollify_subset hc _),he _ (subset_mollifierEnlargement _)] using hp

theorem rawCutoff_high_order_test_extension
    (hφ : Continuous φ) (J : List (Fin n) → Space n → ℝ)
    (hloc : ∀ L, L.length ≤ q → ∀ K : Set (Space n), IsCompact K →
      MemLp (J L) 2 (volume.restrict K))
    (hweak : ∀ L, L.length < q → ∀ i,
      HasLocalWeakCoordinateDerivative (J L) (J (i::L)) i)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (htest : ∀ (ψ : Space n → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∑ I : Fin q → Fin n, ∫ x,
        J (List.ofFn I) x*coordinatePotentialTensor ψ q I x ∂potentialMeasure φ)=0) :
    (∑ I : Fin q → Fin n, ∫ x,
      J (List.ofFn I) x*rawCutoffJet J χ q I x ∂potentialMeasure φ)=0 := by
  have hp (I : Fin q → Fin n) := local_weighted_pairing_mollify hφ
    (rawCutoffJet_memLp J hloc hχ hc (le_refl q) I)
    (rawCutoffJet_hasCompactSupport J hc q I)
    (hloc (List.ofFn I) (by simp))
  have hs := tendsto_finsetSum Finset.univ (fun I _ => hp I)
  have he (k : ℕ) :
      (∑ I : Fin q → Fin n, ∫ x,
        J (List.ofFn I) x*mollify k (rawCutoffJet J χ q I) x ∂potentialMeasure φ)=0 := by
    simp_rw [←coordinatePotentialTensor_rawMollifiedCutoffPotential J hloc hweak hχ hc q (le_refl q)]
    exact htest _ (rawMollifiedCutoffPotential_contDiff J hloc hχ hc k)
      (rawMollifiedCutoffPotential_hasCompactSupport J hc k)
  simp only [he,Finset.sum_const_zero] at hs
  exact tendsto_nhds_unique hs tendsto_const_nhds

theorem poweredCutoff_high_order_test_extension
    (hφ : Continuous φ) (J : List (Fin n) → Space n → ℝ)
    (hloc : ∀ L, L.length ≤ q → ∀ K : Set (Space n), IsCompact K →
      MemLp (J L) 2 (volume.restrict K))
    (hweak : ∀ L, L.length < q → ∀ i,
      HasLocalWeakCoordinateDerivative (J L) (J (i::L)) i)
    (htest : ∀ (ψ : Space n → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∑ I : Fin q → Fin n, ∫ x,
        J (List.ofFn I) x*coordinatePotentialTensor ψ q I x ∂potentialMeasure φ)=0) (hq : q ≠ 0) (k : ℕ) :
    (∑ I : Fin q → Fin n, ∫ x,
      J (List.ofFn I) x*poweredTensorCutoffJet J q k I x ∂potentialMeasure φ)=0 := by
  have hη : ContDiff ℝ (⊤ : ℕ∞) (smoothCutoff n k) :=
    (unitCutoff n).contDiff.comp (contDiff_id.const_smul _)
  have hcη : HasCompactSupport (smoothCutoff n k) := smoothCutoff_hasCompactSupport k
  have hcp : HasCompactSupport (fun x => (smoothCutoff n k x)^(2*q)) :=
    hcη.comp_left (show (0 : ℝ)^(2*q)=0 by apply zero_pow; omega)
  exact rawCutoff_high_order_test_extension hφ J hloc hweak (hη.pow _) hcp htest

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.poweredCutoff_high_order_test_extension

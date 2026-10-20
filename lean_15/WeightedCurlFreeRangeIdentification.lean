import WeightedHodgeLiouville
import WeightedCurlFreeSubspace
import KLS.WeightedFaithfulGraph

/-! Actual rank-one compatible fields are exactly the closed weighted
gradient range. The distributional converse is proved via the genuine
weighted Hodge kernel theorem, not assumed as a domain-density premise. -/
open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped Topology ContDiff BigOperators RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]

theorem weightedGradientProjection_residual_divergenceFree
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (F : CenteredL2.Family (potentialMeasure φ) (Fin n)) :
    WeakWeightedDivergenceFree φ
      (fun i x => (F - weightedGradientProjection hφ hκ hlower F) i x) := by
  intro ψ hψ hc
  have hψ2 := memLp_of_continuous_hasCompactSupport hφ.continuous hψ.continuous hc
  have hd (i : Fin n) : MemLp (coordinateDerivative ψ i) 2 (potentialMeasure φ) :=
    memLp_of_continuous_hasCompactSupport hφ.continuous
      (contDiff_coordinateDerivative hψ (m := 0) (by simp) i).continuous
      (hasCompactSupport_coordinateDerivative hc i)
  obtain ⟨U, _, hU⟩ := exists_weightedH1_of_faithful_test hφ.continuous
    ⟨(hψ.of_le (by simp) : ContDiff ℝ 1 ψ).locallyLipschitz, hψ2⟩
    (energy_lt_top_of_memLp_coordinateDerivative hd)
  have he := weightedGradientProjection_residual_orthogonal hφ hκ hlower F U
  rw [PiLp.inner_apply] at he
  have hi (i : Fin n) :
      inner ℝ ((F - weightedGradientProjection hφ hκ hlower F) i)
        (weightedH1Gradient φ U i) =
        ∫ x, (F - weightedGradientProjection hφ hκ hlower F) i x *
          coordinateDerivative ψ i x ∂potentialMeasure φ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hU i] with x hx
    simp only [weightedH1Gradient_apply, hx, RCLike.inner_apply, conj_trivial]
    ring
  simpa only [hi] using he

/-- Every genuinely distributionally curl-free weighted-L² field has the
actual centered weak primitive already constructed by the Dirichlet form. -/
theorem weightedGradientRange_eq_curlFreeSubspace
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a)) :
    LinearMap.range (weightedH1Gradient φ).toLinearMap =
      weightedCurlFreeSubspace (hφ.of_le (by simp)) := by
  apply le_antisymm
  · exact weightedGradientRange_le_curlFreeSubspace (hφ.of_le (by simp))
  · intro F hF
    let P := weightedGradientProjection (hφ.of_le (by simp)) hκ hlower
    let R := F - P F
    have hR : R ∈ weightedCurlFreeSubspace (hφ.of_le (by simp)) :=
      (weightedCurlFreeSubspace _).sub_mem hF
        (weightedGradientProjection_mem_curlFreeSubspace (hφ.of_le (by simp)) hκ hlower F)
    have hcurl : DistributionallyCurlFree (fun i x => R i x) :=
      (mem_weightedCurlFreeSubspace_iff (hφ.of_le (by simp)) R).mp hR
    have hdiv : WeakWeightedDivergenceFree φ (fun i x => R i x) :=
      weightedGradientProjection_residual_divergenceFree (hφ.of_le (by simp)) hκ hlower F
    have hz := weightedHodge_kernel_eq_zero hφ hκ hlower (fun i => Lp.memLp (R i)) hcurl hdiv
    have hRzero : R = 0 := by
      apply PiLp.ext
      intro i
      apply Lp.ext
      filter_upwards [hz i, Lp.coeFn_zero ℝ 2 (potentialMeasure φ)] with x hx hy
      exact hx.trans hy.symm
    refine ⟨weightedGradientPrimitive (hφ.of_le (by simp)) hκ hlower F, ?_⟩
    change P F = F
    exact (sub_eq_zero.mp hRzero).symm

theorem weightedGradientPrimitive_reconstruct_curlFree
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (F : CenteredL2.Family (potentialMeasure φ) (Fin n))
    (hF : F ∈ weightedCurlFreeSubspace (hφ.of_le (by simp))) :
    weightedH1Gradient φ (weightedGradientPrimitive (hφ.of_le (by simp)) hκ hlower F) = F := by
  rw [← weightedGradientRange_eq_curlFreeSubspace hφ hκ hlower] at hF
  obtain ⟨U, rfl⟩ := hF
  change weightedH1Gradient φ
    (weightedGradientPrimitive (hφ.of_le (by simp)) hκ hlower (weightedH1Gradient φ U)) =
      weightedH1Gradient φ U
  rw [weightedGradientPrimitive_gradient]

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.weightedGradientProjection_residual_divergenceFree
#print axioms KLS.DeterministicBridgeIntegration.weightedGradientRange_eq_curlFreeSubspace
#print axioms KLS.DeterministicBridgeIntegration.weightedGradientPrimitive_reconstruct_curlFree

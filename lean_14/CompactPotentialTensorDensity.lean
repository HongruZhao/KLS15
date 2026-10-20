import GlobalTensorCutoffLimit

/-! Genuine density of compact C∞ potential tensors in every actual
distributionally compatible symmetric tensor Hilbert space (paper B.1).
This is ordinary tensor L² density, not projected-divergence graph density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n r s : ℕ} {φ χ : Space n → ℝ}

lemma orderedTensorField_tendsto_of_coordinate {F : ℕ → OrderedTensorField φ r}
    {G : OrderedTensorField φ r} (h : ∀ I, Tendsto (fun k => F k I) atTop (𝓝 (G I))) :
    Tendsto F atTop (𝓝 G) := by
  have ht : Tendsto (fun k => (fun I => F k I)) atTop (𝓝 (fun I => G I)) :=
    tendsto_pi_nhds.mpr h
  have he := (PiLp.continuous_toLp (p := (2 : ENNReal))
    (fun _ : OrderedTensorIndex n r => Lp ℝ 2 (potentialMeasure φ))).tendsto (fun I => G I) |>.comp ht
  simpa only [Function.comp_def, WithLp.toLp_ofLp] using he

def cutoffTensorJetLp (hφ : Continuous φ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (U : (k : ℕ) → OrderedTensorField φ k) (r : ℕ) :
    OrderedTensorField φ r :=
  WithLp.toLp 2 (fun I => (memLp_potentialMeasure_of_memLp_volume_compact hφ
    (tensorCutoffJet_memLp hφ hχ hc U r I)
    (tensorCutoffJet_hasCompactSupport hc U r I)).toLp (tensorCutoffJet U χ r I))

theorem cutoffTensorJetLp_smoothCutoff_tendsto (hφ : Continuous φ)
    (U : (k : ℕ) → OrderedTensorField φ k) (r : ℕ) :
    Tendsto (fun k => cutoffTensorJetLp hφ (smoothCutoff_contDiff_top k)
      (smoothCutoff_hasCompactSupport k) U r) atTop (𝓝 (U r)) := by
  apply orderedTensorField_tendsto_of_coordinate
  intro I
  have hm (k : ℕ) := memLp_potentialMeasure_of_memLp_volume_compact hφ
    (tensorCutoffJet_memLp hφ (smoothCutoff_contDiff_top k) (smoothCutoff_hasCompactSupport k) U r I)
    (tensorCutoffJet_hasCompactSupport (smoothCutoff_hasCompactSupport k) U r I)
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun k => tensorCutoffJet U (smoothCutoff n k) r I) hm (U r I) (Lp.memLp _)).mpr
      (eLpNorm_tensorCutoffJet_smoothCutoff_sub_tendsto_zero U r I)
  change Tendsto (fun k => (hm k).toLp (tensorCutoffJet U (smoothCutoff n k) r I)) atTop (𝓝 (U r I))
  simpa only [Lp.toLp_coeFn] using ht

theorem compactPotentialTensorLp_mollifiedCutoff_tendsto (hφ : ContDiff ℝ 1 φ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (U : (k : ℕ) → OrderedTensorField φ k)
    (hgraph : ∀ k, k < s → ∃ V : TensorPrimitive (φ := φ) (OrderedTensorIndex n k),
      finitePrimitiveValue (OrderedTensorIndex n k) V = U k ∧
        ∀ I i, weightedH1Derivative φ i (V I) = U (k + 1) (Fin.cons i I))
    (r : ℕ) (hr : r ≤ s) :
    Tendsto (fun k => compactPotentialTensorLp hφ.continuous
      (mollifiedCutoffPotential_contDiff hφ.continuous hχ hc U k)
      (mollifiedCutoffPotential_hasCompactSupport hc U k) r) atTop
        (𝓝 (cutoffTensorJetLp hφ.continuous hχ hc U r)) := by
  apply orderedTensorField_tendsto_of_coordinate
  intro I
  have hm (k : ℕ) := memLp_of_continuous_hasCompactSupport hφ.continuous
    (coordinatePotentialTensor_contDiff
      (mollifiedCutoffPotential_contDiff hφ.continuous hχ hc U k) r I).continuous
    (coordinatePotentialTensor_hasCompactSupport
      (mollifiedCutoffPotential_hasCompactSupport hc U k) r I)
  have hg := memLp_potentialMeasure_of_memLp_volume_compact hφ.continuous
    (tensorCutoffJet_memLp hφ.continuous hχ hc U r I)
    (tensorCutoffJet_hasCompactSupport hc U r I)
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hm _ hg).mpr
    (eLpNorm_mollifiedCutoffPotential_derivative_sub_tendsto_zero hφ hχ hc U hgraph r hr I)

def compactPotentialTensorSet (hφ : Continuous φ) (r : ℕ) : Set (OrderedTensorField φ r) :=
  {F | ∃ (ψ : Space n → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ),
    compactPotentialTensorLp hφ hψ hc r = F}

lemma compactPotentialTensorSet_subset_compatible (hφ : ContDiff ℝ 1 φ) (r : ℕ) :
    compactPotentialTensorSet hφ.continuous r ⊆
      (compatibleSymmetricTensorSubspace hφ r : Set (OrderedTensorField φ r)) := by
  rintro F ⟨ψ, hψ, hc, rfl⟩
  exact compactPotentialTensorLp_mem hφ hψ hc r

variable [IsProbabilityMeasure (potentialMeasure φ)]
variable {κ : ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ),
    κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

include hκ hlower in
/-- Paper B.1's actual compact-potential density, for the full distributional
compatible symmetric tensor class at every rank. -/
theorem closure_compactPotentialTensorSet_eq_compatible (r : ℕ) :
    closure (compactPotentialTensorSet hφ.continuous r) =
      (compatibleSymmetricTensorSubspace (hφ.of_le (by simp)) r : Set (OrderedTensorField φ r)) := by
  apply subset_antisymm
  · exact (compatibleSymmetricTensorSubspace_isClosed (hφ.of_le (by simp)) r).closure_subset_iff.mpr
      (compactPotentialTensorSet_subset_compatible (hφ.of_le (by simp)) r)
  · intro F hF
    obtain ⟨U, htop, _, _, hgraph, _⟩ := exists_iterated_compatibleTensorPrimitive hφ hκ hlower r ⟨F, hF⟩
    have hin (k : ℕ) : cutoffTensorJetLp hφ.continuous (smoothCutoff_contDiff_top k)
        (smoothCutoff_hasCompactSupport k) U r ∈ closure (compactPotentialTensorSet hφ.continuous r) := by
      apply isClosed_closure.mem_of_tendsto
        (compactPotentialTensorLp_mollifiedCutoff_tendsto (hφ.of_le (by simp))
          (smoothCutoff_contDiff_top k) (smoothCutoff_hasCompactSupport k) U hgraph r le_rfl)
      exact Eventually.of_forall fun m => subset_closure ⟨_, _, _, rfl⟩
    have he := isClosed_closure.mem_of_tendsto (cutoffTensorJetLp_smoothCutoff_tendsto hφ.continuous U r)
      (Eventually.of_forall hin)
    rwa [htop] at he

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.compactPotentialTensorLp_mollifiedCutoff_tendsto
#print axioms KLS.DeterministicBridgeIntegration.closure_compactPotentialTensorSet_eq_compatible

import KLS.MomentPotentialCompactness

/-! Compactness for vector-valued Lipschitz maps anchored at the origin.
Unlike the earlier bounded-target potential compactness theorem, this
applies to actual source gradients with a common Hessian bound while the
target radii increase. -/
noncomputable section
open Filter Set
open scoped Topology NNReal
namespace KLSConstantImprovement.ActualAnchoredLipschitzCompactness405
open KLS
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

def anchoredLipschitzMaps (n m : ℕ) (L : ℝ≥0) : Set C(Space n, Space m) :=
  {f | LipschitzWith L f ∧ f 0 = 0}

theorem anchored_lipschitz_bound {L : ℝ≥0} {f : Space n → Space m}
    (hL : LipschitzWith L f) (h0 : f 0 = 0) (x : Space n) :
    ‖f x‖ ≤ L * ‖x‖ := by
  have h := hL.dist_le_mul x 0
  simpa only [h0, dist_zero_right] using h

theorem isCompact_anchoredLipschitzMaps (L : ℝ≥0) :
    IsCompact (anchoredLipschitzMaps n m L) := by
  have hc : IsClosed {f : Space n → Space m | LipschitzWith L f ∧ f 0 = 0} :=
    (isClosed_setOfPred_lipschitzWith L).inter
      (isClosed_eq (continuous_apply 0) continuous_const)
  have hp : IsCompact {f : Space n → Space m | LipschitzWith L f ∧ f 0 = 0} := by
    apply IsCompact.of_isClosed_subset
      (isCompact_univ_pi (fun x : Space n =>
        isCompact_closedBall (0 : Space m) ((L : ℝ) * ‖x‖))) hc
    intro f hf x _
    simpa only [Metric.mem_closedBall, dist_zero_right] using anchored_lipschitz_bound hf.1 hf.2 x
  apply ArzelaAscoli.isCompact_of_equicontinuous
  · have heq : ContinuousMap.toFun '' anchoredLipschitzMaps n m L =
        {f : Space n → Space m | LipschitzWith L f ∧ f 0 = 0} := by
      ext f
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact hg
      · intro hf
        exact ⟨⟨f, hf.1.continuous⟩, hf, rfl⟩
    rw [heq]
    exact hp
  · exact (LipschitzWith.uniformEquicontinuous
      (fun f : anchoredLipschitzMaps n m L => (f.1 : Space n → Space m)) L
      (fun f => f.2.1)).equicontinuous

theorem exists_subseq_anchoredLipschitzMaps (L : ℝ≥0) (f : ℕ → Space n → Space m)
    (hL : ∀ k, LipschitzWith L (f k)) (h0 : ∀ k, f k 0 = 0) :
    ∃ (g : Space n → Space m) (s : ℕ → ℕ),
      StrictMono s ∧ LipschitzWith L g ∧ g 0 = 0 ∧
      TendstoLocallyUniformly (fun k => f (s k)) g atTop ∧
      ∀ K : Set (Space n), IsCompact K → TendstoUniformlyOn (fun k => f (s k)) g atTop K := by
  let F : ℕ → C(Space n, Space m) := fun k => ⟨f k, (hL k).continuous⟩
  have hF (k : ℕ) : F k ∈ anchoredLipschitzMaps n m L := ⟨hL k, h0 k⟩
  obtain ⟨g, hg, s, hs, hlim⟩ := (isCompact_anchoredLipschitzMaps (n := n) (m := m) L).tendsto_subseq hF
  refine ⟨g, s, hs, hg.1, hg.2, ?_, ?_⟩
  · exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hlim
  · exact ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hlim

end KLSConstantImprovement.ActualAnchoredLipschitzCompactness405
#print axioms KLSConstantImprovement.ActualAnchoredLipschitzCompactness405.anchored_lipschitz_bound
#print axioms KLSConstantImprovement.ActualAnchoredLipschitzCompactness405.isCompact_anchoredLipschitzMaps
#print axioms KLSConstantImprovement.ActualAnchoredLipschitzCompactness405.exists_subseq_anchoredLipschitzMaps

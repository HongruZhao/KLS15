import MollifiedTensorPotential

/-! Actual all-order bounds for the released expanding smooth cutoffs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory InnerProductSpace Set Matrix Filter ContinuousLinearMap
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ}

lemma directionalWordDerivative_map_const_smul {f : Space n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℝ) (L : List (Space n)) (x : Space n) :
    directionalWordDerivative f (L.map (fun v => c • v)) x =
      c ^ L.length * directionalWordDerivative f L x := by
  induction L generalizing x with
  | nil => simp only [List.map_nil, List.length_nil, pow_zero, one_mul]
  | cons v L ih =>
    have he : directionalWordDerivative f (L.map (fun v => c • v)) =
        fun y => c ^ L.length * directionalWordDerivative f L y := funext ih
    simp only [List.map_cons, directionalWordDerivative_cons, he, List.length_cons]
    have hd := (((contDiff_directionalWordDerivative hf L).differentiable (by simp)) x).hasFDerivAt.const_mul
      (c ^ L.length)
    rw [hd.fderiv]
    simp only [_root_.smul_apply, smul_eq_mul, map_smul, pow_succ]
    ring

lemma coordinateWordDerivative_comp_const_smul {f : Space n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℝ) (L : List (Fin n)) (x : Space n) :
    coordinateWordDerivative (fun y => f (c • y)) L x =
      c ^ L.length * coordinateWordDerivative f L (c • x) := by
  have he := directionalWordDerivative_comp_affine hf
    (c • ContinuousLinearMap.id ℝ (Space n)) 0
    (L.map (fun i => EuclideanSpace.single i 1)) x
  simp only [zero_add, _root_.smul_apply, ContinuousLinearMap.id_apply] at he
  change directionalWordDerivative (fun y => f (c • y))
    (L.map (fun i => EuclideanSpace.single i 1)) x = _
  rw [he]
  change directionalWordDerivative f
    ((L.map (fun i => EuclideanSpace.single i 1)).map (fun v => c • v)) (c • x) = _
  rw [directionalWordDerivative_map_const_smul hf]
  simp only [List.length_map, coordinateWordDerivative]

theorem smoothCutoff_coordinateWord_bound (L : List (Fin n)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ k x,
      ‖coordinateWordDerivative (smoothCutoff n k) L x‖ ≤ cutoffScale k ^ L.length * K := by
  obtain ⟨K, hK⟩ := (coordinateWordDerivative_hasCompactSupport (unitCutoff n).hasCompactSupport L).exists_bound_of_continuous
    (coordinateWordDerivative_contDiff (unitCutoff n).contDiff L).continuous
  refine ⟨K, (norm_nonneg _).trans (hK 0), ?_⟩
  intro k x
  change ‖coordinateWordDerivative (fun y => unitCutoff n (cutoffScale k • y)) L x‖ ≤ _
  rw [coordinateWordDerivative_comp_const_smul (unitCutoff n).contDiff, norm_mul,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (cutoffScale_pos k).le _)]
  exact mul_le_mul_of_nonneg_left (hK _) (pow_nonneg (cutoffScale_pos k).le _)

theorem smoothCutoff_coordinateWord_uniform_bound (L : List (Fin n)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ k x, ‖coordinateWordDerivative (smoothCutoff n k) L x‖ ≤ K := by
  obtain ⟨K, hK, hb⟩ := smoothCutoff_coordinateWord_bound L
  refine ⟨K, hK, fun k x => (hb k x).trans ?_⟩
  exact mul_le_of_le_one_left hK
    (pow_le_one₀ (cutoffScale_pos k).le (cutoffScale_le_one k))

theorem smoothCutoff_coordinateWord_tendsto_zero (L : List (Fin n)) (hne : L ≠ []) (x : Space n) :
    Tendsto (fun k => coordinateWordDerivative (smoothCutoff n k) L x) atTop (𝓝 0) := by
  obtain ⟨K, _, hb⟩ := smoothCutoff_coordinateWord_bound L
  apply squeeze_zero_norm (fun k => hb k x)
  have hlen : L.length ≠ 0 := by simpa using hne
  simpa only [zero_pow hlen, zero_mul] using (cutoffScale_tendsto_zero.pow L.length).mul_const K

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.smoothCutoff_coordinateWord_bound
#print axioms KLS.DeterministicBridgeIntegration.smoothCutoff_coordinateWord_tendsto_zero

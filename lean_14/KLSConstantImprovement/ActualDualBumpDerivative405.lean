import KLSConstantImprovement.ActualDualKatoMultiplier405

/-! The common (u,p) cutoff has one uniform local-L2 derivative dominator
and is eventually constant at every actual point. This controls the error
when removing the compact joint cutoff from nonlinear weak tests. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualDualBumpDerivative405
open KLS ActualBoundedCanonicalSource ActualNaturalDualJoint405 ActualDualBumpControl405
open ActualVectorDifferential405 ActualSourceNaturalHessian405 ActualSmoothScalarTruncation405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {n : ℕ} {μ : Measure (Space n)}

theorem dualBump_nonnegative_le_one (k : ℕ) (v : DualIndex n → ℝ) :
    0 ≤ dualBump k v ∧ dualBump k v ≤ 1 := by
  refine ⟨Finset.prod_nonneg fun a _ => scalarBump.nonneg, ?_⟩
  exact Finset.prod_le_one₀ (fun a _ => scalarBump.nonneg) (fun a _ => scalarBump.le_one)

theorem dualBump_directional_bound {L : NNReal} (hL : ∀ k, LipschitzWith L (dualBump (n := n) k))
    (k : ℕ) (v z : DualIndex n → ℝ) :
    ‖fderiv ℝ (dualBump k) v z‖ ≤ (L : ℝ) * ∑ a : DualIndex n, ‖z a‖ := by
  rw [fderiv_eq_sum_vectorPartial]
  calc
    _ ≤ ∑ a : DualIndex n, ‖vectorPartial (dualBump k) a v * z a‖ := norm_sum_le _ _
    _ ≤ ∑ a : DualIndex n, (L : ℝ) * ‖z a‖ := Finset.sum_le_sum fun a _ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (vectorPartial_bound (hL k) a v) (norm_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

def dualDerivativeNormSum (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) (a : Fin n) (x : Space n) : ℝ :=
  ∑ b : DualIndex n, ‖dualDerivative d g Du b a x‖

theorem dualDerivativeNormSum_local_L2 (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hDu : ∀ i a E, IsCompact E → MemLp (Du i a) 2 (volume.restrict E))
    (hC : ∀ i a E, IsCompact E → MemLp (fun x => naturalCanonicalHessian d g Du x i a) 2 (volume.restrict E))
    (a : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (dualDerivativeNormSum d g Du a) 2 (volume.restrict E) := by
  unfold dualDerivativeNormSum
  apply memLp_finsetSum Finset.univ
  intro b _
  cases b with
  | inl i => exact (hDu i a E hE).norm
  | inr i => exact (hC i a E hE).norm

theorem actual_dual_bump_eventually (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) (x : Space n) :
    ∀ᶠ k in atTop, dualSource d g (dualBump k) x = 1 ∧
      ∀ a : Fin n, dualSourceDerivative d g Du (dualBump k) a x = 0 := by
  filter_upwards [dualBump_eventually_one_nhds (fun b => dualValue d g b x),
    dualBump_eventually_fderiv_zero (fun b => dualValue d g b x)] with k hk hd
  refine ⟨hk.eq_of_nhds, fun a => ?_⟩
  unfold dualSourceDerivative
  rw [hd]
  rfl

end KLSConstantImprovement.ActualDualBumpDerivative405
#print axioms KLSConstantImprovement.ActualDualBumpDerivative405.dualBump_nonnegative_le_one
#print axioms KLSConstantImprovement.ActualDualBumpDerivative405.dualBump_directional_bound
#print axioms KLSConstantImprovement.ActualDualBumpDerivative405.dualDerivativeNormSum_local_L2
#print axioms KLSConstantImprovement.ActualDualBumpDerivative405.actual_dual_bump_eventually

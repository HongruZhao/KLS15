import KLSConstantImprovement.ActualSourceRegularizedEnergyForm405

/-!
For 0 < epsilon <= 1 the constructed scalar inverse has an ordinary H1
bound uniform in both regularization parameters. The finite constant is
proved from the actual source's ordinary gap and is used only for weak
compactness and inverse identification. It does not enter the independent
Gaffney bound, whose final right-hand side is the forcing L2 norm squared.
-/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceRegularizedInverseUniformH1405
open KLS ActualBoundedCanonicalSource ActualSourceOrdinaryPoincare405
open ActualSourceRegularizedEnergyForm405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem exists_regularizedOrdinaryInverse_uniform_H1_bound
    (d : SourceData μ) (hn : 1 ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ k ε (hε : 0 < ε), ε ≤ 1 →
      ∀ g : Lp ℝ 2 (potentialMeasure d.potential),
        ‖regularizedOrdinaryInverse d hn k hε g‖ ≤ K * ‖g‖ := by
  obtain ⟨C, hC, hP⟩ := exists_source_ordinary_H1_poincare d hn
  let M : ℝ := 4 / d.targetConvexityConstant
  have hM : 0 < M := by have hκ := d.target_convexity_pos; dsimp [M]; positivity
  let c : ℝ := (M + 1)⁻¹
  have hc : 0 < c := inv_pos.mpr (by dsimp [M]; positivity)
  have hCp : 0 < 1 + C := by linarith
  let a : ℝ := c * (1 + C)⁻¹
  have ha : 0 < a := mul_pos hc (inv_pos.mpr hCp)
  refine ⟨a⁻¹, inv_pos.mpr ha, ?_⟩
  intro k ε hε hε1 g
  let U := regularizedOrdinaryInverse d hn k hε g
  let E : ℝ := ∑ i : Fin n, ‖weightedH1Derivative d.potential i U‖^2
  have hE : 0 ≤ E := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hp := hP U
  have hnrm := weightedH1_norm_sq d.potential U
  have hnorm : ‖U‖^2 ≤ (1 + C) * E := by change ‖U‖^2 ≤ _; dsimp [E] at *; nlinarith
  have hvalue : ‖weightedH1Value d.potential U‖ ≤ ‖U‖ := by
    nlinarith [norm_nonneg (weightedH1Value d.potential U), norm_nonneg U]
  have hcinv : c ≤ (M + ε)⁻¹ := by
    simpa only [c, one_div] using one_div_le_one_div_of_le
      (show 0 < M + ε by positivity) (show M + ε ≤ M + 1 by linarith)
  have hlo : a * ‖U‖^2 ≤ regularizedOrdinaryEnergyForm d k hε U U := by
    calc
      _ = c * ((1 + C)⁻¹ * ‖U‖^2) := by dsimp [a]; ring
      _ ≤ c * E := mul_le_mul_of_nonneg_left ((inv_mul_le_iff₀ hCp).mpr hnorm) hc.le
      _ ≤ (M + ε)⁻¹ * E := mul_le_mul_of_nonneg_right hcinv hE
      _ ≤ _ := regularizedOrdinaryEnergyForm_lower d k hε U
  have hvar := regularizedOrdinaryInverse_variational d hn k hε g U
  have hi : regularizedOrdinaryEnergyForm d k hε U U ≤ ‖g‖ * ‖U‖ := by
    rw [hvar]
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hvalue (norm_nonneg g))
  by_cases hU : ‖U‖ = 0
  · rw [hU]
    positivity
  have hUp : 0 < ‖U‖ := lt_of_le_of_ne (norm_nonneg U) (Ne.symm hU)
  have hamul : a * ‖U‖ ≤ ‖g‖ :=
    (mul_le_mul_iff_right₀ hUp).mp (by nlinarith [hlo.trans hi])
  exact (le_inv_mul_iff₀ ha).mpr hamul

end KLSConstantImprovement.ActualSourceRegularizedInverseUniformH1405
#print axioms KLSConstantImprovement.ActualSourceRegularizedInverseUniformH1405.exists_regularizedOrdinaryInverse_uniform_H1_bound

import KLSConstantImprovement.ActualResponseWeightedEnergy405

/-! The weighted response-row norm is the literal actual H energy.
This binds the first-order scalar response estimate to the same source
matrix field used in production. -/
noncomputable section
open MeasureTheory Matrix InnerProductSpace Filter
open scoped BigOperators
namespace KLSConstantImprovement.ActualResponseIntegralEnergy405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualWeakCanonicalMetricOrdinaryGraph ActualWeakCanonicalMetricResponse
open ActualResponseWeightedEnergy405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem sourceResponseWeightedRow_coe (d : SourceData μ)
    (e : Fin n → Lp ℝ 2 (potentialMeasure d.potential)) (j : Fin n) :
    (sourceResponseWeightedRow d e j : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      fun x => ∑ i, canonicalMetricUnroot d.potential x i j * e i x := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => sourceUnrootMultiplier d i j (e i)),
    ae_all_iff.mpr (fun i => sourceUnrootMultiplier_coe d i j (e i))] with x hx hm
  change (∑ i, sourceUnrootMultiplier d i j (e i)) x = _
  rw [hx]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => hm i

theorem actual_response_rows_square_identity (d : SourceData μ)
    (e : Fin n → Lp ℝ 2 (potentialMeasure d.potential)) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      (∑ j, sourceResponseWeightedRow d e j x ^ 2) =
        ∑ a, ∑ b, coordinateHessian d.potential x a b * e a x * e b x := by
  filter_upwards [d.hessian_ae_source, ae_all_iff.mpr (sourceResponseWeightedRow_coe d e)]
    with x hx he
  let S := canonicalMetricUnroot d.potential x
  let v : Fin n → ℝ := fun i => e i x
  have hS : S.IsSymm := (inverseSqrtMatrix_isSymm (coordinateHessian d.potential x)).inv
  have hrow (j : Fin n) : sourceResponseWeightedRow d e j x = (S *ᵥ v) j := by
    rw [he j]
    apply Finset.sum_congr rfl
    intro i _
    change S i j * v i = S j i * v i
    rw [hS.apply j i]
  calc
    _ = (S *ᵥ v) ⬝ᵥ (S *ᵥ v) := by simp only [hrow, dotProduct, pow_two]
    _ = v ⬝ᵥ (coordinateHessian d.potential x *ᵥ v) := by
      rw [← Matrix.dotProduct_transpose_mulVec S v (S *ᵥ v), Matrix.mulVec_mulVec,
        canonicalMetricUnroot_gram_at hx.1]
    _ = _ := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, v]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring

theorem actual_response_vector_energy_integrable (d : SourceData μ)
    (e : Fin n → Lp ℝ 2 (potentialMeasure d.potential)) :
    Integrable (fun x => ∑ a, ∑ b,
      coordinateHessian d.potential x a b * e a x * e b x) (potentialMeasure d.potential) := by
  exact (integrable_finsetSum Finset.univ (fun j _ =>
    (Lp.memLp (sourceResponseWeightedRow d e j)).integrable_sq)).congr
      (actual_response_rows_square_identity d e)

theorem actual_response_rows_norm_integral (d : SourceData μ)
    (e : Fin n → Lp ℝ 2 (potentialMeasure d.potential)) :
    (∑ j, ‖sourceResponseWeightedRow d e j‖ ^ 2) =
      ∫ x, ∑ a, ∑ b, coordinateHessian d.potential x a b * e a x * e b x
        ∂potentialMeasure d.potential := by
  simp_rw [L2.norm_sq_eq_integral_sq]
  rw [← integral_finsetSum Finset.univ (fun j _ =>
    (Lp.memLp (sourceResponseWeightedRow d e j)).integrable_sq)]
  exact integral_congr_ae (actual_response_rows_square_identity d e)

theorem actual_response_norm_le_H_energy (d : SourceData μ)
    (e : Fin n → Lp ℝ 2 (potentialMeasure d.potential)) :
    ‖sourceResponse d e‖ ^ 2 ≤
      ∫ x, ∑ a, ∑ b, coordinateHessian d.potential x a b * e a x * e b x
        ∂potentialMeasure d.potential := by
  rw [← actual_response_rows_norm_integral]
  exact actual_response_norm_le_weighted_rows d e

end KLSConstantImprovement.ActualResponseIntegralEnergy405
#print axioms KLSConstantImprovement.ActualResponseIntegralEnergy405.actual_response_rows_square_identity
#print axioms KLSConstantImprovement.ActualResponseIntegralEnergy405.actual_response_vector_energy_integrable
#print axioms KLSConstantImprovement.ActualResponseIntegralEnergy405.actual_response_rows_norm_integral
#print axioms KLSConstantImprovement.ActualResponseIntegralEnergy405.actual_response_norm_le_H_energy

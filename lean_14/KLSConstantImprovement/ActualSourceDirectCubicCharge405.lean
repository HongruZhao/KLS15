import KLSConstantImprovement.ActualSourceDirectCubicBalance405

/-! Integrated direct-cubic charge on the actual source. The signed
H/G cross energy is retained, and the remainder is the literal ordered
commutator square. Every integral domain is already proved from SourceData. -/
noncomputable section
open Matrix MeasureTheory Filter
open scoped BigOperators
namespace KLSConstantImprovement.ActualSourceDirectCubicCharge405
open KLS ActualBoundedCanonicalSource ActualSourceQuarticBinding405 ActualSourceHessianEvolution405
open ActualDirectCubicPointwise405 ActualSourceDirectCubicEnergy405
open ActualSourceDirectCubicBalance405
variable {n : ℕ} {μ : Measure (Space n)}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem actual_direct_integrated_commutator_identity (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j) :
    (∫ x, actualDirectGammaEnergy d T x ∂potentialMeasure d.potential) -
      (∫ x, actualDirectCrossEnergy d T x ∂potentialMeasure d.potential) / 2 =
      (1 / 2 : ℝ) * ∫ x, directCubicCommutatorCharge (coordinateHessian d.potential x) T
        (sourceThirdMatrix d x) ∂potentialMeasure d.potential := by
  calc
    _ = ∫ x, actualDirectGammaEnergy d T x - actualDirectCrossEnergy d T x / 2
        ∂potentialMeasure d.potential := by
      rw [integral_sub (actual_direct_gamma_integrable d T)
        ((actual_direct_cross_integrable d T).div_const 2), integral_div]
    _ = ∫ x, (1 / 2 : ℝ) * directCubicCommutatorCharge (coordinateHessian d.potential x) T
        (sourceThirdMatrix d x) ∂potentialMeasure d.potential :=
      integral_congr_ae (actual_direct_cubic_commutator_square d T hT12 hT23)
    _ = _ := integral_const_mul _ _

theorem actual_direct_commutator_integral_nonnegative (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ ∫ x, directCubicCommutatorCharge (coordinateHessian d.potential x) T
      (sourceThirdMatrix d x) ∂potentialMeasure d.potential :=
  integral_nonneg fun x => directCubicCommutatorCharge_nonnegative _ _ _

theorem actual_direct_cubic_curvature_charge_identity (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j) :
    (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) +
      2 * (∫ x, actualDirectTargetCurvature d T x ∂potentialMeasure d.potential) +
      (∫ x, directCubicCommutatorCharge (coordinateHessian d.potential x) T
        (sourceThirdMatrix d x) ∂potentialMeasure d.potential) =
      3 * ∫ x, actualDirectFullCurvature d T x ∂potentialMeasure d.potential := by
  have hb := actual_direct_cubic_primitive_identity d T
  have hc := actual_direct_integrated_commutator_identity d T hT12 hT23
  have hs : (∫ x, actualDirectFullCurvature d T x ∂potentialMeasure d.potential) =
      (∫ x, actualDirectTargetCurvature d T x ∂potentialMeasure d.potential) +
      ∫ x, actualDirectGammaEnergy d T x ∂potentialMeasure d.potential := by
    simp_rw [actual_direct_full_curvature_split]
    exact integral_add (actual_direct_target_curvature_integrable d T) (actual_direct_gamma_integrable d T)
  linarith

theorem actual_direct_cross_retained_cap (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j) :
    3 * (∫ x, actualDirectCrossEnergy d T x ∂potentialMeasure d.potential) ≤
      2 * ((∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) -
        ∫ x, actualDirectTargetCurvature d T x ∂potentialMeasure d.potential) := by
  have hb := actual_direct_cubic_primitive_identity d T
  have hc := actual_direct_cross_energy_bound d T hT12 hT23
  linarith

theorem actual_direct_cross_moment_cap (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j) :
    3 * (∫ x, actualDirectCrossEnergy d T x ∂potentialMeasure d.potential) ≤
      2 * ∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential := by
  have hc := actual_direct_cross_retained_cap d T hT12 hT23
  have hp := actual_direct_target_curvature_nonnegative d T
    (fun i => Matrix.IsSymm.ext fun j k => hT23 i k j)
  linarith

end KLSConstantImprovement.ActualSourceDirectCubicCharge405

#print axioms KLSConstantImprovement.ActualSourceDirectCubicCharge405.actual_direct_integrated_commutator_identity
#print axioms KLSConstantImprovement.ActualSourceDirectCubicCharge405.actual_direct_cubic_curvature_charge_identity
#print axioms KLSConstantImprovement.ActualSourceDirectCubicCharge405.actual_direct_cross_moment_cap

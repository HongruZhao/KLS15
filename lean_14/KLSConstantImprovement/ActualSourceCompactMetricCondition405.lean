import KLSConstantImprovement.ActualIntrinsicSourceCompactRange405
import KLSConstantImprovement.ActualSourceInverseMetricRegularization405
import KLSConstantImprovement.ActualSourceRadialConnectionDomains405
import KLSConstantImprovement.ActualCompatibleRadialExtra405
import KLSConstantImprovement.ActualSourceCompactConnectionAbsorption405

/-! A compact condition bound for the actual metric pays the signed extra
term in Euclidean radial H testing. Constants depend on the source compact
set. No global condition number or natural mass bound is asserted. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal
namespace KLSConstantImprovement.ActualSourceCompactMetricCondition405
open KLS ActualBoundedCanonicalSource ActualIntrinsicSourceCompactRange405
open ActualSourceConnectionFields405 ActualSourceConnectionPointwise405
open ActualSourceRadialConnectionDomains405 ActualCompatibleRadialExtra405
open ActualSourceCompactConnectionAbsorption405 ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

private theorem norm_toLp_sq (u : Fin n → ℝ) :
    ‖(WithLp.toLp 2 u : Space n)‖ ^ 2 = u ⬝ᵥ u := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, PiLp.toLp_apply, dotProduct]

private theorem inner_toLp_quadratic (A : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) :
    inner ℝ (WithLp.toLp 2 u : Space n) (matrixAction A (WithLp.toLp 2 u)) = u ⬝ᵥ (A *ᵥ u) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, PiLp.toLp_apply,
    matrixAction_apply, dotProduct, Matrix.mulVec]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem jointMass_eq_quadratic (u : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    ActualIntrinsicJointWeakTests405.jointMass (Sum.elim u (fun ij => H ij.1 ij.2)) =
      u ⬝ᵥ (H *ᵥ u) := by
  simp only [ActualIntrinsicJointWeakTests405.jointMass, Sum.elim_inl, Sum.elim_inr,
    dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem actual_compact_metric_quadratic_bounds (d : SourceData μ)
    (E : Set (Space n)) (hE : IsCompact E) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
      ∀ᵐ x ∂(potentialMeasure d.potential).restrict E, ∀ u : Fin n → ℝ,
        α * (u ⬝ᵥ u) ≤ u ⬝ᵥ (coordinateHessian d.potential x *ᵥ u) ∧
        u ⬝ᵥ (coordinateHessian d.potential x *ᵥ u) ≤ β * (u ⬝ᵥ u) ∧
        u ⬝ᵥ ((coordinateHessian d.potential x)⁻¹ *ᵥ u) ≤ α⁻¹ * (u ⬝ᵥ u) := by
  obtain ⟨α, G, hα, _hG, hlow, _hentry⟩ := actual_source_joint_metric_range d E hE
  let β : ℝ := 16 / d.targetConvexityConstant
  have hβ : 0 < β := by have hκ := d.target_convexity_pos; dsimp only [β]; positivity
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  refine ⟨α, β, hα, hβ, ?_⟩
  filter_upwards [hlow.filter_mono (hac.restrict E).ae_le,
    ae_restrict_of_ae d.hessian_ae_source,
    ae_restrict_of_ae (d.hessian_operator_bound_ae.filter_mono hac.ae_le)] with x hx hp hOp
  have hlo (u : Fin n → ℝ) : α * (u ⬝ᵥ u) ≤ u ⬝ᵥ (coordinateHessian d.potential x *ᵥ u) := by
    have hu := hx u
    simpa only [dotProduct, ← pow_two, jointMass_eq_quadratic] using hu
  intro u
  refine ⟨hlo u, ?_, matrix_inverse_quadratic_le_of_lower_bound hp.1 hα hlo u⟩
  let v : Space n := WithLp.toLp 2 u
  have hnorm : ‖matrixAction (coordinateHessian d.potential x) v‖ ≤ β * ‖v‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hOp (norm_nonneg v))
  have hinner := (real_inner_le_norm v (matrixAction (coordinateHessian d.potential x) v)).trans
    (mul_le_mul_of_nonneg_left hnorm (norm_nonneg v))
  have he : ‖v‖ * (β * ‖v‖) = β * ‖v‖ ^ 2 := by ring
  rw [he] at hinner
  simpa only [v, norm_toLp_sq, inner_toLp_quadratic] using hinner

theorem exists_actual_compact_radial_extra_bound (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i a => Du i a x)).IsSymm)
    (E : Set (Space n)) (hE : IsCompact E) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ δ : ℝ, 0 ≤ δ →
      ∀ᵐ x ∂(potentialMeasure d.potential).restrict E,
        |2 * δ * sourceRadialExtra d (naturalCanonicalFlux d g) Du x /
          ActualRadialMatrixCalculus405.radialDenom δ (fun a => naturalCanonicalFlux d g a x) ^ 2| ≤
        sourceConnectionGamma d (naturalCanonicalFlux d g) x /
          (4 * ActualRadialMatrixCalculus405.radialDenom δ (fun a => naturalCanonicalFlux d g a x)) +
        4 * c * sourceVectorJacobianEnergy Du x /
          ActualRadialMatrixCalculus405.radialDenom δ (fun a => naturalCanonicalFlux d g a x) := by
  obtain ⟨α, β, hα, hβ, hbounds⟩ := actual_compact_metric_quadratic_bounds d E hE
  refine ⟨β * α⁻¹, by positivity, ?_⟩
  intro δ hδ
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  let u := naturalCanonicalFlux d g
  filter_upwards [hbounds, ae_restrict_of_ae d.hessian_ae_source,
    ae_restrict_of_ae (sourceThirdAlong_isSymm_ae d u),
    ae_restrict_of_ae (hcomp.filter_mono hac.ae_le),
    ae_restrict_of_ae (sourceConnectionGamma_nonnegative_ae d u),
    ae_restrict_of_ae (sourceVectorJacobianEnergy_nonnegative_ae d Du hcomp)] with x hx hp hN hB hΓ hQ
  let H := coordinateHessian d.potential x
  let B := Matrix.of (fun i a => Du i a x)
  let N := sourceThirdAlong d u x
  let U : ℝ := (fun i => u i x) ⬝ᵥ (fun i => u i x)
  have hUn : 0 ≤ U := Finset.sum_nonneg fun i _ => mul_self_nonneg (u i x)
  have he := compatible_radial_extra_square H B N hp.1 hB hN (fun i => u i x)
  have hm : 0 ≤ (fun i => u i x) ⬝ᵥ (H *ᵥ (fun i => u i x)) :=
    hp.1.posSemidef.dotProduct_mulVec_nonneg _
  have hi : 0 ≤ (fun i => u i x) ⬝ᵥ (H⁻¹ *ᵥ (fun i => u i x)) :=
    hp.1.inv.posSemidef.dotProduct_mulVec_nonneg _
  have hprod : ((fun i => u i x) ⬝ᵥ (H *ᵥ (fun i => u i x))) *
      ((fun i => u i x) ⬝ᵥ (H⁻¹ *ᵥ (fun i => u i x))) ≤ (β * α⁻¹) * U ^ 2 := by
    have hh := mul_le_mul (hx (fun i => u i x)).2.1 (hx (fun i => u i x)).2.2 hi
      (mul_nonneg hβ.le hUn)
    simpa only [H, U, mul_assoc, mul_left_comm, mul_comm, pow_two] using hh
  have htrace : (B * B).trace = sourceVectorJacobianEnergy Du x := by
    simp only [B, sourceVectorJacobianEnergy, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
  rw [sourceThirdAlong_trace_square, htrace] at he
  have hb : sourceRadialExtra d u Du x ^ 2 ≤
      (β * α⁻¹) * sourceConnectionGamma d u x * sourceVectorJacobianEnergy Du x * U ^ 2 := by
    rw [sourceRadialExtra_contraction]
    have hh := mul_le_mul_of_nonneg_left hprod (mul_nonneg hΓ hQ)
    exact he.trans (by nlinarith only [hh])
  simpa only [U, dotProduct, ← pow_two, ActualRadialMatrixCalculus405.radialDenom,
    ActualRadialMatrixCalculus405.radialSquare] using
      radial_extra_young hΓ hQ hUn hδ (by positivity : 0 ≤ β * α⁻¹) hb

end KLSConstantImprovement.ActualSourceCompactMetricCondition405
#print axioms KLSConstantImprovement.ActualSourceCompactMetricCondition405.actual_compact_metric_quadratic_bounds
#print axioms KLSConstantImprovement.ActualSourceCompactMetricCondition405.exists_actual_compact_radial_extra_bound

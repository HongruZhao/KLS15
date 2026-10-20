import KLSConstantImprovement.ActualSourceGaffneyAbsorption405
import KLSConstantImprovement.ActualSourceRegularizedFluxCompatibility405

/-! The coercivity parameter in the Gaffney absorption theorem is paid
by the actual regularized metric and actual weak flux compatibility. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceRegularizedJacobianCoercivity405
open KLS ActualBoundedCanonicalSource ActualSourceMetricRegularization405
open ActualSourceRegularizedEnergyForm405 ActualSourceRegularizedFluxH1405
open ActualSourceRegularizedFluxCompatibility405 ActualCompatibleJacobianCoercivity405
open ActualSourceLocalizedGaffney405 ActualSourceGaffneyAbsorption405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

private lemma matrixAction_toLp_quadratic (M : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) :
    inner ℝ (WithLp.toLp 2 a : Space n) (matrixAction M (WithLp.toLp 2 a)) =
      a ⬝ᵥ (M *ᵥ a) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    matrixAction_apply, PiLp.toLp_apply, dotProduct, Matrix.mulVec]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private lemma norm_toLp_sq_eq_dotProduct (a : Fin n → ℝ) :
    ‖(WithLp.toLp 2 a : Space n)‖ ^ 2 = a ⬝ᵥ a := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, PiLp.toLp_apply, dotProduct]

theorem regularizedMetricHessian_loewner_bounds (d : SourceData μ) (k : ℕ)
    (ε : ℝ) (x : Space n) :
    (regularizedMetricHessian d k ε x - ε • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
      ((4 / d.targetConvexityConstant + ε) • (1 : Matrix (Fin n) (Fin n) ℝ) -
        regularizedMetricHessian d k ε x).PosSemidef := by
  have hH : (regularizedMetricHessian d k ε x).IsHermitian :=
    (actual_mollified_metric_posDef d k x).isHermitian.add
      (Matrix.isHermitian_one.smul (IsSelfAdjoint.all ε))
  refine ⟨?_, ?_⟩
  · simpa only [regularizedMetricHessian, add_sub_cancel_right] using
      (actual_mollified_metric_posDef d k x).posSemidef
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · exact (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _)).sub hH
    intro b
    have hb := (regularizedMetricHessian_quadratic_bounds d k ε x (WithLp.toLp 2 b)).2
    have hq : b ⬝ᵥ (regularizedMetricHessian d k ε x *ᵥ b) ≤
        (4 / d.targetConvexityConstant + ε) * (b ⬝ᵥ b) := by
      simpa only [norm_toLp_sq_eq_dotProduct, matrixAction_toLp_quadratic] using hb
    simpa only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul] using sub_nonneg.mpr hq

theorem regularizedFluxJacobian_coercive_ae (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (D : Fin n → Fin n → Space n → ℝ)
    (hc : ∀ᵐ x ∂(volume : Measure (Space n)),
      (regularizedMetricHessian d k ε x * regularizedFluxJacobian d hn k hε g D x).IsSymm) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      (ε / (4 / d.targetConvexityConstant + ε)) *
          sourceVectorJacobianSquare (regularizedFluxDerivative d hn k hε g D) x ≤
        sourceVectorJacobianEnergy (regularizedFluxDerivative d hn k hε g D) x := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) :=
    withDensity_absolutelyContinuous _ _
  have hcν := hc.filter_mono hac.ae_le
  filter_upwards [hcν] with x hx
  have hβ : 0 < 4 / d.targetConvexityConstant + ε := by
    have hκ := d.target_convexity_pos
    positivity
  have hh := regularizedMetricHessian_loewner_bounds d k ε x
  have he := compatible_jacobian_trace_coercive (regularizedMetricHessian d k ε x)
    (regularizedFluxJacobian d hn k hε g D x) (regularizedMetricHessian_posDef d k hε x)
    hx hε.le hβ hh.1 hh.2
  simpa only [sourceVectorJacobianSquare, sourceVectorJacobianEnergy, matrixFrobeniusSq,
    regularizedFluxJacobian, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply] using he

end KLSConstantImprovement.ActualSourceRegularizedJacobianCoercivity405
#print axioms KLSConstantImprovement.ActualSourceRegularizedJacobianCoercivity405.regularizedMetricHessian_loewner_bounds
#print axioms KLSConstantImprovement.ActualSourceRegularizedJacobianCoercivity405.regularizedFluxJacobian_coercive_ae

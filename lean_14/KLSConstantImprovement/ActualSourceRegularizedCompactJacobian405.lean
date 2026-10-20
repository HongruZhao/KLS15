import KLSConstantImprovement.ActualSourceRegularizedGaffney405

/-! Compact Jacobian coercivity is uniform in both metric parameters.
It uses the actual uniform compact lower Hessian bound, rather than the
epsilon floor used only to establish each global derivative domain. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceRegularizedCompactJacobian405
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

theorem exists_regularizedFluxJacobian_uniform_compact_coercivity (d : SourceData μ)
    (hn : 1 ≤ n) {E : Set (Space n)} (hE : IsCompact E) :
    ∃ c : ℝ, 0 < c ∧ ∀ k ε (hε : 0 < ε), ε ≤ 1 →
      ∀ (g : Lp ℝ 2 (potentialMeasure d.potential)) (D : Fin n → Fin n → Space n → ℝ),
      (∀ᵐ x ∂(volume : Measure (Space n)),
        (regularizedMetricHessian d k ε x * regularizedFluxJacobian d hn k hε g D x).IsSymm) →
      ∀ᵐ x ∂(potentialMeasure d.potential).restrict E,
        c * sourceVectorJacobianSquare (regularizedFluxDerivative d hn k hε g D) x ≤
          sourceVectorJacobianEnergy (regularizedFluxDerivative d hn k hε g D) x := by
  obtain ⟨m, hm, hfloor⟩ := regularizedMetricHessian_compact_lower d hE
  let β : ℝ := 4 / d.targetConvexityConstant + 1
  have hβ : 0 < β := by have hκ := d.target_convexity_pos; dsimp only [β]; positivity
  refine ⟨m / β, div_pos hm hβ, ?_⟩
  intro k ε hε hε1 g D hc
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) :=
    withDensity_absolutelyContinuous _ _
  have hcn : ∀ᵐ x ∂(potentialMeasure d.potential).restrict E,
      (regularizedMetricHessian d k ε x * regularizedFluxJacobian d hn k hε g D x).IsSymm :=
    (hc.filter_mono hac.ae_le).filter_mono (ae_mono (Measure.restrict_le_self (s := E)))
  filter_upwards [hcn, ae_restrict_mem hE.measurableSet] with x hx hxE
  let H := regularizedMetricHessian d k ε x
  have hH : H.PosDef := regularizedMetricHessian_posDef d k hε x
  have hlo : (H - m • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · exact hH.isHermitian.sub (Matrix.isHermitian_one.smul (IsSelfAdjoint.all m))
    intro b
    have hb := hfloor k ε hε.le x hxE (WithLp.toLp 2 b)
    have hq : m * (b ⬝ᵥ b) ≤ b ⬝ᵥ (H *ᵥ b) := by
      simpa only [H, norm_toLp_sq_eq_dotProduct, matrixAction_toLp_quadratic] using hb
    simpa only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul] using sub_nonneg.mpr hq
  have hup : (β • (1 : Matrix (Fin n) (Fin n) ℝ) - H).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · exact (Matrix.isHermitian_one.smul (IsSelfAdjoint.all β)).sub hH.isHermitian
    intro b
    have hb := (regularizedMetricHessian_quadratic_bounds d k ε x (WithLp.toLp 2 b)).2
    have hq : b ⬝ᵥ (H *ᵥ b) ≤ β * (b ⬝ᵥ b) := by
      have hb' : b ⬝ᵥ (H *ᵥ b) ≤ (4 / d.targetConvexityConstant + ε) * (b ⬝ᵥ b) := by
        simpa only [H, norm_toLp_sq_eq_dotProduct, matrixAction_toLp_quadratic] using hb
      exact hb'.trans (mul_le_mul_of_nonneg_right (by dsimp only [β]; linarith) (show 0 ≤ b ⬝ᵥ b from Finset.sum_nonneg (fun i _ => mul_self_nonneg (b i))))
    simpa only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul] using sub_nonneg.mpr hq
  have he := compatible_jacobian_trace_coercive H (regularizedFluxJacobian d hn k hε g D x)
    hH hx hm.le hβ hlo hup
  simpa only [sourceVectorJacobianSquare, sourceVectorJacobianEnergy, matrixFrobeniusSq,
    regularizedFluxJacobian, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply] using he

end KLSConstantImprovement.ActualSourceRegularizedCompactJacobian405
#print axioms KLSConstantImprovement.ActualSourceRegularizedCompactJacobian405.exists_regularizedFluxJacobian_uniform_compact_coercivity

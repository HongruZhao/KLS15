import KLSConstantImprovement.ActualBoundedCanonicalSource
import KLS.WeakMomentMollifiedEllipticity
import KLS.C11HessianMollification
import KLS.QuadraticAlexandrovViscosity

/-!
Actual smooth metric regularization on the original source weight.
Only the metric Hessian is mollified and supplied with an epsilon floor;
the probability law remains e^(-phi) dx. Global and compact ellipticity
and convergence are consequences of the existing actual weak source.
No Monge--Ampere equation is asserted for the surrogate metric.
-/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceMetricRegularization405
open KLS ActualBoundedCanonicalSource
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

def regularizedMetricHessian (d : SourceData μ) (k : ℕ) (ε : ℝ) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ :=
  coordinateHessian (mollify k d.potential) x + ε • (1 : Matrix (Fin n) (Fin n) ℝ)

theorem actual_mollified_metric_posDef (d : SourceData μ) (k : ℕ) (x : Space n) :
    (coordinateHessian (mollify k d.potential) x).PosDef := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  exact (weak_moment_mollify_posDef_and_det_lower d.source_lipschitz d.source_convex
    d.target_smooth.continuous d.target_closed d.target_convex
    (d.pushforward.trans d.target_representation) k x).1

theorem actual_mollified_metric_quadratic_upper (d : SourceData μ)
    (k : ℕ) (x v : Space n) :
    inner ℝ v (matrixAction (coordinateHessian (mollify k d.potential) x) v) ≤
      (4 / d.targetConvexityConstant) * ‖v‖ ^ 2 := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hs : ContDiff ℝ 2 (mollify k d.potential) :=
    (mollify_contDiff d.source_C1.continuous.locallyIntegrable k).of_le (by simp)
  have he : inner ℝ v (matrixAction (coordinateHessian (mollify k d.potential) x) v) =
      ∑ i : Fin n, ∑ j : Fin n, coordinateHessian (mollify k d.potential) x i j * v i * v j := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, matrixAction_apply,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, coordinateHessian_quadratic_eq hs]
  exact (weak_moment_mollify_hessian_upper d.source_lipschitz d.source_convex
    (d.target_smooth.of_le (by simp)) d.target_convex_potential d.target_convexity_pos
    d.target_strong d.target_closed d.target_convex
    (d.pushforward.trans d.target_representation) k x).1 v

theorem regularizedMetricHessian_contDiff (d : SourceData μ) (k : ℕ) (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (regularizedMetricHessian d k ε) := by
  unfold regularizedMetricHessian
  apply ContDiff.add _ contDiff_const
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact contDiff_coordinateHessian
    (mollify_contDiff d.source_C1.continuous.locallyIntegrable k) (m := (⊤ : ℕ∞)) (by simp) i j

theorem regularizedMetricHessian_posDef (d : SourceData μ) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (x : Space n) : (regularizedMetricHessian d k ε x).PosDef := by
  exact (actual_mollified_metric_posDef d k x).add (Matrix.PosDef.one.smul hε)

theorem regularizedMetricHessian_quadratic_bounds (d : SourceData μ)
    (k : ℕ) (ε : ℝ) (x v : Space n) :
    ε * ‖v‖ ^ 2 ≤ inner ℝ v (matrixAction (regularizedMetricHessian d k ε x) v) ∧
      inner ℝ v (matrixAction (regularizedMetricHessian d k ε x) v) ≤
        (4 / d.targetConvexityConstant + ε) * ‖v‖ ^ 2 := by
  have hlo : 0 ≤ inner ℝ v (matrixAction (coordinateHessian (mollify k d.potential) x) v) := by
    exact inner_matrixAction_nonneg (actual_mollified_metric_posDef d k x).posSemidef v
  have hup := actual_mollified_metric_quadratic_upper d k x v
  unfold regularizedMetricHessian
  rw [matrixAction_add_matrices, matrixAction_smul_scalar, matrixAction_one_apply,
    inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
  constructor <;> nlinarith

/-- The compact lower metric bound is independent of both regularization
parameters, and holds for every actual mollifier in the retained sequence. -/
theorem regularizedMetricHessian_compact_lower (d : SourceData μ)
    {E : Set (Space n)} (hE : IsCompact E) :
    ∃ m : ℝ, 0 < m ∧ ∀ k ε, 0 ≤ ε → ∀ x ∈ E, ∀ v : Space n,
      m * ‖v‖ ^ 2 ≤ inner ℝ v (matrixAction (regularizedMetricHessian d k ε x) v) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  obtain ⟨B, m, Λ, _, hm, _, hell⟩ := weak_moment_mollified_hessian_uniformly_elliptic_on_compact
    d.source_lipschitz d.source_convex (d.target_smooth.of_le (by simp)) d.target_convex_potential
    d.target_convexity_pos d.target_strong d.target_closed d.target_convex
    (d.pushforward.trans d.target_representation) hE
  refine ⟨m, hm, ?_⟩
  intro k ε hε x hx v
  have hlo := ((hell k x hx).2.2 v).1
  unfold regularizedMetricHessian
  rw [matrixAction_add_matrices, matrixAction_smul_scalar, matrixAction_one_apply,
    inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
  exact hlo.trans (le_add_of_nonneg_right (mul_nonneg hε (sq_nonneg _)))

theorem regularizedMetricHessian_tendsto_ae (d : SourceData μ) :
    ∀ᵐ x ∂(volume : Measure (Space n)),
      Tendsto (fun k => regularizedMetricHessian d k (cutoffScale k) x)
        atTop (𝓝 (coordinateHessian d.potential x)) := by
  filter_upwards [coordinateHessian_mollify_tendsto_ae_of_gradient_lipschitz
    d.source_lipschitz d.gradient_lipschitz] with x hx
  have hε : Tendsto (fun k => cutoffScale k • (1 : Matrix (Fin n) (Fin n) ℝ))
      atTop (𝓝 0) := by simpa using cutoffScale_tendsto_zero.smul_const (1 : Matrix (Fin n) (Fin n) ℝ)
  simpa only [regularizedMetricHessian, add_zero] using hx.add hε

end KLSConstantImprovement.ActualSourceMetricRegularization405
#print axioms KLSConstantImprovement.ActualSourceMetricRegularization405.actual_mollified_metric_posDef
#print axioms KLSConstantImprovement.ActualSourceMetricRegularization405.actual_mollified_metric_quadratic_upper
#print axioms KLSConstantImprovement.ActualSourceMetricRegularization405.regularizedMetricHessian_contDiff
#print axioms KLSConstantImprovement.ActualSourceMetricRegularization405.regularizedMetricHessian_posDef
#print axioms KLSConstantImprovement.ActualSourceMetricRegularization405.regularizedMetricHessian_quadratic_bounds
#print axioms KLSConstantImprovement.ActualSourceMetricRegularization405.regularizedMetricHessian_compact_lower
#print axioms KLSConstantImprovement.ActualSourceMetricRegularization405.regularizedMetricHessian_tendsto_ae

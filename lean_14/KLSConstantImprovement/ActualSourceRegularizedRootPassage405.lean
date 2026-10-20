import KLSConstantImprovement.ActualSourceRegularizedJacobianCoercivity405
import KLSConstantImprovement.ActualWeakCanonicalMetricOrdinaryGraph
import KLSConstantImprovement.ActualSourceInverseMetricRegularization405

/-! The actual regularized root coefficients converge to the actual
source roots. Compact inverse-root bounds are uniform in both metric
parameters; direct-root bounds are global for epsilon at most one. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceRegularizedRootPassage405
open KLS ActualBoundedCanonicalSource ActualSourceMetricRegularization405
open ActualSourceInverseMetricRegularization405 ActualSourceRegularizedJacobianCoercivity405
open ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricCore ActualWeakCanonicalMetricOrdinaryGraph
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

def regularizedMetricRoot (d : SourceData μ) (k : ℕ) (ε : ℝ) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ := inverseSqrtMatrix (regularizedMetricHessian d k ε x)

def regularizedMetricUnroot (d : SourceData μ) (k : ℕ) (ε : ℝ) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ := (regularizedMetricRoot d k ε x)⁻¹

private theorem inverseSqrt_gram (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    (inverseSqrtMatrix A).transpose * inverseSqrtMatrix A = A⁻¹ := by
  rw [(inverseSqrtMatrix_isSymm A).eq]
  unfold inverseSqrtMatrix
  rw [← Matrix.mul_inv_rev, CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]

theorem regularizedMetricRoots_tendsto_ae (d : SourceData μ) :
    ∀ᵐ x ∂(volume : Measure (Space n)),
      Tendsto (fun k => regularizedMetricRoot d k (cutoffScale k) x)
        atTop (𝓝 (canonicalMetricRoot d.potential x)) ∧
      Tendsto (fun k => regularizedMetricUnroot d k (cutoffScale k) x)
        atTop (𝓝 (canonicalMetricUnroot d.potential x)) := by
  filter_upwards [regularizedMetricHessian_tendsto_ae d, d.hessian_ae] with x hx hp
  have ht : Tendsto (fun k => regularizedMetricHessian d k (cutoffScale k) x) atTop
      (𝓝[{A : Matrix (Fin n) (Fin n) ℝ | A.PosDef}] (coordinateHessian d.potential x)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hx, Eventually.of_forall fun k =>
      regularizedMetricHessian_posDef d k (cutoffScale_pos k) x⟩
  have hR : Tendsto (fun k => regularizedMetricRoot d k (cutoffScale k) x) atTop
      (𝓝 (canonicalMetricRoot d.potential x)) :=
    (locallyLipschitzOn_inverseSqrtMatrix_posDef.continuousOn
      (coordinateHessian d.potential x) hp.1).tendsto.comp ht
  refine ⟨hR, ?_⟩
  exact (matrix_inverse_continuousAt_posDef (canonicalMetricRoot_posDef_at hp.1)).tendsto.comp hR

theorem regularizedMetricRoot_uniform_compact_entry_bound (d : SourceData μ)
    {E : Set (Space n)} (hE : IsCompact E) :
    ∃ B : ℝ, 0 < B ∧ ∀ k ε, 0 < ε → ∀ x ∈ E, ∀ i j,
      ‖regularizedMetricRoot d k ε x i j‖ ≤ B := by
  obtain ⟨C, hC, hb⟩ := regularizedMetricInverse_compact_entry_bound d hE
  refine ⟨C + 1, by linarith, ?_⟩
  intro k ε hε x hx i j
  have hg := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A j j)
    (inverseSqrt_gram (regularizedMetricHessian d k ε x) (regularizedMetricHessian_posDef d k hε x))
  have hs : regularizedMetricRoot d k ε x i j ^ 2 ≤ regularizedMetricInverse d k ε x j j := by
    calc
      _ ≤ ∑ a : Fin n, regularizedMetricRoot d k ε x a j ^ 2 :=
        Finset.single_le_sum (fun a _ => sq_nonneg (regularizedMetricRoot d k ε x a j)) (Finset.mem_univ i)
      _ = _ := by simpa only [regularizedMetricRoot, regularizedMetricUnroot, regularizedMetricInverse,
        Matrix.mul_apply, Matrix.transpose_apply, pow_two] using hg
  have hdiag : regularizedMetricInverse d k ε x j j ≤ C :=
    (le_abs_self _).trans (hb k ε hε x hx j j)
  rw [Real.norm_eq_abs]
  nlinarith [sq_nonneg C, sq_abs (regularizedMetricRoot d k ε x i j), abs_nonneg (regularizedMetricRoot d k ε x i j)]

theorem regularizedMetricUnroot_uniform_entry_bound (d : SourceData μ)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (x : Space n) (i j : Fin n) :
    ‖regularizedMetricUnroot d k ε x i j‖ ≤ 4 / d.targetConvexityConstant + 2 := by
  let M : ℝ := 4 / d.targetConvexityConstant
  have hM : 0 < M := div_pos (by norm_num) d.target_convexity_pos
  have hg := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A j j)
    (inverseSqrtMatrix_inverse_gram (regularizedMetricHessian_posDef d k hε x))
  have hs : regularizedMetricUnroot d k ε x i j ^ 2 ≤ regularizedMetricHessian d k ε x j j := by
    calc
      _ ≤ ∑ a : Fin n, regularizedMetricUnroot d k ε x a j ^ 2 :=
        Finset.single_le_sum (fun a _ => sq_nonneg (regularizedMetricUnroot d k ε x a j)) (Finset.mem_univ i)
      _ = _ := by simpa only [regularizedMetricRoot, regularizedMetricUnroot, regularizedMetricInverse,
        Matrix.mul_apply, Matrix.transpose_apply, pow_two] using hg
  have hdiag : regularizedMetricHessian d k ε x j j ≤ M + ε := by
    have hh : 0 ≤ ((M + ε) • (1 : Matrix (Fin n) (Fin n) ℝ) - regularizedMetricHessian d k ε x) j j :=
      (regularizedMetricHessian_loewner_bounds d k ε x).2.diag_nonneg
    simpa only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      sub_nonneg] using hh
  rw [Real.norm_eq_abs]
  change |regularizedMetricUnroot d k ε x i j| ≤ M + 2
  nlinarith [sq_nonneg M, sq_abs (regularizedMetricUnroot d k ε x i j), abs_nonneg (regularizedMetricUnroot d k ε x i j)]

end KLSConstantImprovement.ActualSourceRegularizedRootPassage405
#print axioms KLSConstantImprovement.ActualSourceRegularizedRootPassage405.regularizedMetricRoots_tendsto_ae
#print axioms KLSConstantImprovement.ActualSourceRegularizedRootPassage405.regularizedMetricRoot_uniform_compact_entry_bound
#print axioms KLSConstantImprovement.ActualSourceRegularizedRootPassage405.regularizedMetricUnroot_uniform_entry_bound

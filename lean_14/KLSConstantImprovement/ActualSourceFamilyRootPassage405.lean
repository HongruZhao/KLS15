import KLSConstantImprovement.ActualSourceUniformEllipticity405
import KLSConstantImprovement.ActualSourceRegularizedRootPassage405
import KLS.WeightedEnergyCoercivity

/-! Actual metric roots for a varying family of canonical sources. AE
Hessian convergence gives AE roots; the common actual Monge--Ampere lower
bound pays the uniform compact inverse-root bounds needed for L2 tests. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped Topology NNReal ContDiff ENNReal BigOperators Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceFamilyRootPassage405
open KLS ActualBoundedCanonicalSource ActualSourceUniformEllipticity405
open ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricCore ActualWeakCanonicalMetricOrdinaryGraph
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {ν : ℕ → Measure (Space n)} {μ : Measure (Space n)}

theorem actual_family_roots_tendsto_ae (d : ∀ k, SourceData (ν k)) (d₀ : SourceData μ)
    (hh : ∀ᵐ x ∂(volume : Measure (Space n)), Tendsto
      (fun k => coordinateHessian (d k).potential x) atTop (𝓝 (coordinateHessian d₀.potential x))) :
    ∀ᵐ x ∂(volume : Measure (Space n)),
      Tendsto (fun k => canonicalMetricRoot (d k).potential x) atTop
        (𝓝 (canonicalMetricRoot d₀.potential x)) ∧
      Tendsto (fun k => canonicalMetricUnroot (d k).potential x) atTop
        (𝓝 (canonicalMetricUnroot d₀.potential x)) := by
  filter_upwards [hh, ae_all_iff.mpr (fun k => (d k).hessian_ae), d₀.hessian_ae] with x hx hk h₀
  have ht : Tendsto (fun k => coordinateHessian (d k).potential x) atTop
      (𝓝[{A : Matrix (Fin n) (Fin n) ℝ | A.PosDef}] (coordinateHessian d₀.potential x)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hx, Eventually.of_forall fun k => (hk k).1⟩
  have hR : Tendsto (fun k => canonicalMetricRoot (d k).potential x) atTop
      (𝓝 (canonicalMetricRoot d₀.potential x)) :=
    (locallyLipschitzOn_inverseSqrtMatrix_posDef.continuousOn
      (coordinateHessian d₀.potential x) h₀.1).tendsto.comp ht
  exact ⟨hR, (matrix_inverse_continuousAt_posDef (canonicalMetricRoot_posDef_at h₀.1)).tendsto.comp hR⟩

theorem actual_family_unroot_uniform_entry_bound
    (d : ∀ k, SourceData (ν k)) {κ : ℝ} (hκ : 0 < κ)
    (hk : ∀ k, κ ≤ (d k).targetConvexityConstant) (k : ℕ) (i j : Fin n) :
    ∀ᵐ x ∂(volume : Measure (Space n)),
      ‖canonicalMetricUnroot (d k).potential x i j‖ ≤ 16/κ+1 := by
  have h := (sourceMetricUnroot_entry_bound (d k) i j).filter_mono
    (volume_absolutelyContinuous_potentialMeasure (d k).source_C1.continuous).ae_le
  filter_upwards [h] with x hx
  exact hx.trans (add_le_add
    (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 16) hκ (hk k)) le_rfl)

theorem actual_family_root_uniform_local_bound
    (d : ∀ k, SourceData (ν k)) {κ L P : ℝ} (hκ : 0 < κ)
    (hk : ∀ k, κ ≤ (d k).targetConvexityConstant)
    (hV : ∀ k p, L ≤ (d k).targetPotential p)
    (E : Set (Space n)) (hp : ∀ k x, x ∈ E → (d k).potential x ≤ P) :
    ∃ B : ℝ, 0 < B ∧ ∀ k,
      ∀ᵐ x ∂(volume : Measure (Space n)), x ∈ E → ∀ i j,
        ‖canonicalMetricRoot (d k).potential x i j‖ ≤ B := by
  obtain ⟨α, β, hα, _hβ, hell⟩ := actual_family_local_ellipticity d hκ hk hV E hp
  refine ⟨α⁻¹+1, by positivity, fun k => ?_⟩
  filter_upwards [hell k] with x hx
  intro hxE i j
  have he := hx hxE
  have hlo (u : Fin n → ℝ) : α * (u ⬝ᵥ u) ≤
      u ⬝ᵥ (coordinateHessian (d k).potential x *ᵥ u) := by
    have hh := (he.2.2.2 (WithLp.toLp 2 u)).1
    have hn : ‖(WithLp.toLp 2 u : Space n)‖ ^ 2 = u ⬝ᵥ u := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, PiLp.toLp_apply, dotProduct]
    have hq : inner ℝ (WithLp.toLp 2 u : Space n)
        (matrixAction (coordinateHessian (d k).potential x) (WithLp.toLp 2 u)) =
        u ⬝ᵥ (coordinateHessian (d k).potential x *ᵥ u) := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
        matrixAction_apply, PiLp.toLp_apply, dotProduct, Matrix.mulVec]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    simpa only [hn, hq] using hh
  have hJ := matrix_inverse_quadratic_le_of_lower_bound he.1 hα hlo (Pi.single j 1)
  have hj : (coordinateHessian (d k).potential x)⁻¹ j j ≤ α⁻¹ := by
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply, single_one_dotProduct,
      dotProduct_single, Pi.single_eq_same, mul_one] using hJ
  have hg := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A j j)
    (canonicalMetricRoot_gram_at he.1)
  have hs : canonicalMetricRoot (d k).potential x i j ^ 2 ≤
      (coordinateHessian (d k).potential x)⁻¹ j j := by
    calc
      _ ≤ ∑ a : Fin n, canonicalMetricRoot (d k).potential x a j ^ 2 :=
        Finset.single_le_sum (fun a _ => sq_nonneg (canonicalMetricRoot (d k).potential x a j))
          (Finset.mem_univ i)
      _ = _ := by simpa only [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using hg
  rw [Real.norm_eq_abs]
  nlinarith [hs.trans hj, sq_nonneg (α⁻¹), sq_abs (canonicalMetricRoot (d k).potential x i j),
    abs_nonneg (canonicalMetricRoot (d k).potential x i j)]

end KLSConstantImprovement.ActualSourceFamilyRootPassage405
#print axioms KLSConstantImprovement.ActualSourceFamilyRootPassage405.actual_family_roots_tendsto_ae
#print axioms KLSConstantImprovement.ActualSourceFamilyRootPassage405.actual_family_unroot_uniform_entry_bound
#print axioms KLSConstantImprovement.ActualSourceFamilyRootPassage405.actual_family_root_uniform_local_bound

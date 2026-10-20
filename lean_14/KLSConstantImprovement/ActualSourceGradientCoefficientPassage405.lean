import KLSConstantImprovement.ActualSourceRegularizedRootMultipliers405
import KLSConstantImprovement.ActualSourceLimitFluxDomains405

/-! Compact coefficients H_k H^(-1/2) converge strongly against actual
L2 tests to H^(1/2).  The measure remains the original source measure. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceGradientCoefficientPassage405
open KLS ActualBoundedCanonicalSource ActualSourceMetricRegularization405
open ActualSourceInverseMetricRegularization405 ActualSourceRegularizedRootPassage405
open ActualBoundedCoefficientL2Passage405 ActualSourceLimitFluxDomains405
open ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricOrdinaryGraph ActualWeakCanonicalMetricCore
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem hessian_mul_canonicalMetricRoot_at {φ : Space n → ℝ} {x : Space n}
    (hp : (coordinateHessian φ x).PosDef) :
    coordinateHessian φ x * canonicalMetricRoot φ x = canonicalMetricUnroot φ x := by
  have hs : (canonicalMetricUnroot φ x).IsSymm :=
    (inverseSqrtMatrix_isSymm (coordinateHessian φ x)).inv
  rw [← canonicalMetricUnroot_gram_at hp, hs.eq, Matrix.mul_assoc,
    canonicalMetricUnroot_mul_root_at hp, Matrix.mul_one]

private theorem cutoffScale_le_one (k : ℕ) : cutoffScale k ≤ 1 := by
  unfold cutoffScale
  apply inv_le_one_of_one_le₀
  linarith [Nat.cast_nonneg (α := ℝ) k]

theorem regularizedMetricHessian_uniform_entry_bound (d : SourceData μ)
    (k : ℕ) (x : Space n) (i j : Fin n) :
    ‖regularizedMetricHessian d k (cutoffScale k) x i j‖ ≤ 4 / d.targetConvexityConstant + 1 := by
  have hu (a : Fin n → ℝ) :
      a ⬝ᵥ (regularizedMetricHessian d k (cutoffScale k) x *ᵥ a) ≤
        (4 / d.targetConvexityConstant + cutoffScale k) * (a ⬝ᵥ a) := by
    have hb := (regularizedMetricHessian_quadratic_bounds d k (cutoffScale k) x (WithLp.toLp 2 a)).2
    have hq (A : Matrix (Fin n) (Fin n) ℝ) :
        inner ℝ (WithLp.toLp 2 a : Space n) (matrixAction A (WithLp.toLp 2 a)) = a ⬝ᵥ (A *ᵥ a) := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
        matrixAction_apply, PiLp.toLp_apply, dotProduct, Matrix.mulVec]
      exact Finset.sum_congr rfl fun b _ => mul_comm _ _
    have hn : ‖(WithLp.toLp 2 a : Space n)‖ ^ 2 = a ⬝ᵥ a := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, PiLp.toLp_apply, dotProduct]
    simpa only [hq, hn] using hb
  have he := matrix_entry_abs_le_of_quadratic_upper
    (regularizedMetricHessian_posDef d k (cutoffScale_pos k) x).posSemidef hu i j
  rw [Real.norm_eq_abs]
  exact he.trans (by linarith [cutoffScale_le_one k])

def compactRegularizedGradientCoefficient (d : SourceData μ) (E : Set (Space n))
    (i a : Fin n) (k : ℕ) : Space n → ℝ :=
  E.indicator (fun x => (regularizedMetricHessian d k (cutoffScale k) x * canonicalMetricRoot d.potential x) i a)

def compactActualGradientCoefficient (d : SourceData μ) (E : Set (Space n))
    (i a : Fin n) : Space n → ℝ := E.indicator (fun x => canonicalMetricUnroot d.potential x i a)

theorem compact_gradient_coefficient_mul_tendsto_L2 (d : SourceData μ)
    {E : Set (Space n)} (hE : IsCompact E) (i a : Fin n)
    {f : Space n → ℝ} (hf : MemLp f 2 (potentialMeasure d.potential)) :
    ∃ (hp : ∀ k, MemLp (fun x => compactRegularizedGradientCoefficient d E i a k x * f x)
        2 (potentialMeasure d.potential))
      (hl : MemLp (fun x => compactActualGradientCoefficient d E i a x * f x)
        2 (potentialMeasure d.potential)),
      Tendsto (fun k => (hp k).toLp (fun x => compactRegularizedGradientCoefficient d E i a k x * f x)) atTop
        (𝓝 (hl.toLp (fun x => compactActualGradientCoefficient d E i a x * f x))) := by
  let ν := potentialMeasure d.potential
  obtain ⟨B, hB, hRb⟩ := regularizedMetricRoot_uniform_compact_entry_bound d hE
  let C : ℝ := 4 / d.targetConvexityConstant + 1
  have hC : 0 < C := by have hκ := d.target_convexity_pos; dsimp only [C]; positivity
  have hac : ν ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  have hR := inverseSqrtMatrix_aestronglyMeasurable_of_ae_posDef
    (measurable_coordinateHessian d.potential) (d.hessian_ae_source.mono fun _ hx => hx.1)
  have ha (k : ℕ) : AEStronglyMeasurable (compactRegularizedGradientCoefficient d E i a k) ν := by
    have hm := ((regularizedMetricHessian_contDiff d k (cutoffScale k)).continuous.aestronglyMeasurable.mul hR)
    exact ((continuous_apply a).comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable hm)).indicator hE.measurableSet
  have hb : AEStronglyMeasurable (compactActualGradientCoefficient d E i a) ν := by
    exact ((continuous_apply a).comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable (sourceMetricUnroot_aestronglyMeasurable d))).indicator hE.measurableSet
  have hrb : ∀ᵐ x ∂ν, ∀ b c : Fin n, x ∈ E → ‖canonicalMetricRoot d.potential x b c‖ ≤ B := by
    filter_upwards [(regularizedMetricRoots_tendsto_ae d).filter_mono hac.ae_le] with x hx
    intro b c hxE
    have ht := (((continuous_apply c).comp (continuous_apply b)).continuousAt.tendsto.comp hx.1)
    apply le_of_tendsto ht.norm
    exact Eventually.of_forall fun k => hRb k (cutoffScale k) (cutoffScale_pos k) x hxE b c
  have hbound (k : ℕ) : ∀ᵐ x ∂ν,
      ‖compactRegularizedGradientCoefficient d E i a k x‖ ≤ (n : ℝ) * C * B := by
    filter_upwards [hrb] with x hx
    by_cases hxE : x ∈ E
    · rw [compactRegularizedGradientCoefficient, indicator_of_mem hxE]
      calc
        _ ≤ ∑ b : Fin n, ‖regularizedMetricHessian d k (cutoffScale k) x i b‖ *
            ‖canonicalMetricRoot d.potential x b a‖ := by
          simpa only [Matrix.mul_apply, norm_mul] using
            norm_sum_le Finset.univ (fun b : Fin n => regularizedMetricHessian d k (cutoffScale k) x i b *
              canonicalMetricRoot d.potential x b a)
        _ ≤ ∑ _ : Fin n, C * B := Finset.sum_le_sum fun b _ =>
          mul_le_mul (regularizedMetricHessian_uniform_entry_bound d k x i b) (hx b a hxE)
            (norm_nonneg _) hC.le
        _ = _ := by simp [mul_assoc]
    · rw [compactRegularizedGradientCoefficient, indicator_of_notMem hxE, norm_zero]
      positivity
  have ht : ∀ᵐ x ∂ν, Tendsto (fun k => compactRegularizedGradientCoefficient d E i a k x) atTop
      (𝓝 (compactActualGradientCoefficient d E i a x)) := by
    filter_upwards [(regularizedMetricHessian_tendsto_ae d).filter_mono hac.ae_le,
      d.hessian_ae_source] with x hx hp
    by_cases hxE : x ∈ E
    · have hm := hx.mul (tendsto_const_nhds (x := canonicalMetricRoot d.potential x))
      have he := (((continuous_apply a).comp (continuous_apply i)).continuousAt.tendsto.comp hm)
      simpa only [compactRegularizedGradientCoefficient, compactActualGradientCoefficient,
        indicator_of_mem hxE, hessian_mul_canonicalMetricRoot_at hp.1, Function.comp_def] using he
    · simp only [compactRegularizedGradientCoefficient, compactActualGradientCoefficient, indicator_of_notMem hxE]
      exact tendsto_const_nhds
  have hbnd : ∀ᵐ x ∂ν, ‖compactActualGradientCoefficient d E i a x‖ ≤ (n : ℝ) * C * B := by
    filter_upwards [ht, ae_all_iff.mpr hbound] with x hx hb'
    exact le_of_tendsto hx.norm (Eventually.of_forall hb')
  exact bounded_coefficient_mul_tendsto_L2 ha hb (by positivity) hbound hbnd ht hf

end KLSConstantImprovement.ActualSourceGradientCoefficientPassage405
#print axioms KLSConstantImprovement.ActualSourceGradientCoefficientPassage405.hessian_mul_canonicalMetricRoot_at
#print axioms KLSConstantImprovement.ActualSourceGradientCoefficientPassage405.regularizedMetricHessian_uniform_entry_bound
#print axioms KLSConstantImprovement.ActualSourceGradientCoefficientPassage405.compact_gradient_coefficient_mul_tendsto_L2

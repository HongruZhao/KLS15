import KLSConstantImprovement.ActualSourceFormCompanions405
import KLSConstantImprovement.ActualSourceConservativeResolvent405
import KLS.SmoothUpperTest

/-!
The actual bounded smooth upper-level test acts continuously on the
source L2 space. Its variational pairing detects the actual AE upper
bound. This supplies the scalar order step of the full form-resolvent
maximum principle, without a strong operator-core assumption.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter InnerProductSpace
open scoped BigOperators ContDiff Topology NNReal ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceUpperTest405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualSourceConservativeResolvent405 ActualSourceFormCompanions405
variable {n : ℕ} {μ : Measure (Space n)}

theorem sourceUpperTest_memLp (d : SourceData μ) (M : ℝ)
    (u : Lp ℝ 2 (potentialMeasure d.potential)) :
    MemLp (fun x => Real.smoothTransition (u x - M)) 2 (potentialMeasure d.potential) := by
  letI := d.source_probability
  apply MemLp.of_bound
    (Real.smoothTransition.continuous.comp_aestronglyMeasurable
      ((Lp.aestronglyMeasurable u).sub aestronglyMeasurable_const)) 1
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _

def sourceUpperTestLp (d : SourceData μ) (M : ℝ)
    (u : Lp ℝ 2 (potentialMeasure d.potential)) : Lp ℝ 2 (potentialMeasure d.potential) :=
  (sourceUpperTest_memLp d M u).toLp (fun x => Real.smoothTransition (u x - M))

theorem sourceUpperTestLp_ae (d : SourceData μ) (M : ℝ)
    (u : Lp ℝ 2 (potentialMeasure d.potential)) :
    (sourceUpperTestLp d M u : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      fun x => Real.smoothTransition (u x - M) := (sourceUpperTest_memLp d M u).coeFn_toLp

theorem sourceUpperTestLp_continuous (d : SourceData μ) (M : ℝ) :
    Continuous (sourceUpperTestLp d M) := by
  obtain ⟨B, hB, hb⟩ := exists_deriv_smoothTransition_bound
  have hη : LipschitzWith (⟨B, hB⟩ : ℝ≥0) Real.smoothTransition :=
    lipschitzWith_of_nnnorm_deriv_le
      ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero)
      (fun x => by exact_mod_cast (hb x).2)
  have hL : LipschitzWith (⟨B, hB⟩ : ℝ≥0) (sourceUpperTestLp d M) := by
    apply LipschitzWith.of_dist_le_mul
    intro f g
    rw [dist_eq_norm, dist_eq_norm]
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub (sourceUpperTestLp d M f) (sourceUpperTestLp d M g),
      sourceUpperTestLp_ae d M f, sourceUpperTestLp_ae d M g, Lp.coeFn_sub f g]
      with x hx hf hg hfg
    rw [hx, Pi.sub_apply, hf, hg, hfg, Pi.sub_apply]
    have he : (f x - M) - (g x - M) = f x - g x := by ring
    simpa only [he] using hη.norm_sub_le (f x - M) (g x - M)
  exact hL.continuous

/-- A nonpositive actual upper-test pairing forces the desired AE bound.
The following resolvent theorem pays this pairing from the actual form. -/
theorem ae_upper_bound_of_upper_test (d : SourceData μ)
    (u g : Lp ℝ 2 (potentialMeasure d.potential)) (M : ℝ)
    (hg : ∀ᵐ x ∂potentialMeasure d.potential, g x ≤ M)
    (hpair : inner ℝ (u - g) (sourceUpperTestLp d M u) ≤ 0) :
    ∀ᵐ x ∂potentialMeasure d.potential, u x ≤ M := by
  let q : Space n → ℝ := fun x => (u x - g x) * Real.smoothTransition (u x - M)
  have hi : Integrable q (potentialMeasure d.potential) := by
    apply ((Lp.memLp (u - g)).integrable_mul (Lp.memLp (sourceUpperTestLp d M u))).congr
    filter_upwards [Lp.coeFn_sub u g, sourceUpperTestLp_ae d M u] with x hx hy
    change (u - g) x * sourceUpperTestLp d M u x =
      (u x - g x) * Real.smoothTransition (u x - M)
    rw [hx, Pi.sub_apply, hy]
  have he : inner ℝ (u - g) (sourceUpperTestLp d M u) =
      ∫ x, q x ∂potentialMeasure d.potential := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub u g, sourceUpperTestLp_ae d M u] with x hx hy
    simp only [RCLike.inner_apply, conj_trivial, hx, hy, Pi.sub_apply, q]
    ring
  have hq : ∀ᵐ x ∂potentialMeasure d.potential, 0 ≤ q x := by
    filter_upwards [hg] with x hx
    by_cases hu : u x ≤ M
    · change 0 ≤ (u x - g x) * Real.smoothTransition (u x - M)
      rw [Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hu), mul_zero]
    · exact mul_nonneg (sub_nonneg.mpr (hx.trans (le_of_not_ge hu)))
        (Real.smoothTransition.nonneg _)
  have hzero : (∫ x, q x ∂potentialMeasure d.potential) = 0 :=
    le_antisymm (he ▸ hpair) (integral_nonneg_of_ae hq)
  have hz := (integral_eq_zero_iff_of_nonneg_ae hq hi).mp hzero
  filter_upwards [hg, hz] with x hx hz'
  by_contra hu
  have hux : M < u x := lt_of_not_ge hu
  have hstrict : 0 < q x := mul_pos (sub_pos.mpr (lt_of_le_of_lt hx hux))
    (Real.smoothTransition.pos_of_pos (sub_pos.mpr hux))
  exact hstrict.ne' hz'

end KLSConstantImprovement.ActualSourceUpperTest405

#print axioms KLSConstantImprovement.ActualSourceUpperTest405.sourceUpperTestLp_continuous
#print axioms KLSConstantImprovement.ActualSourceUpperTest405.ae_upper_bound_of_upper_test

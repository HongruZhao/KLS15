import KLSConstantImprovement.ActualSourceCovariance405
import KLSConstantImprovement.AffineSameTestSeed238452BellmanEndpoint
import KLS.AffinePotentialCutoff
import KLS.WeightedOptimalPoincare
import KLS.FaithfulPoincareSmoothCore

/-!
Per-law ordinary source Poincare/coercivity. The retained universal bound is
applied to the actual covariance-whitened source. The affine pullback is
proved on compact C3 tests, then the proved faithful smooth-core theorem
extends it to the source's original test class and completed ordinary H1.
The resulting constant may depend on the actual source covariance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix
open scoped BigOperators ContDiff Topology ENNReal NNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceOrdinaryPoincare405
open KLS ActualBoundedCanonicalSource ActualSourceCovariance405
variable {n : ℕ} {μ : Measure (Space n)}

private theorem compact_gradient_sq_integrable {ρ : Measure (Space n)} [IsFiniteMeasure ρ]
    {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    Integrable (fun x => ‖gradient f x‖ ^ 2) ρ := by
  have hg : MemLp (gradient f) 2 ρ :=
    (continuous_gradient_of_contDiff hf).memLp_of_hasCompactSupport
      (hasCompactSupport_gradient hc)
  exact hg.norm.integrable_sq

private theorem compact_real_poincare_of_mem {ρ : Measure (Space n)} [IsProbabilityMeasure ρ]
    {C : ℝ≥0} (hC : C ∈ poincareConstants ρ)
    {f : Space n → ℝ} (hf : ContDiff ℝ 3 f) (hc : HasCompactSupport f) :
    ProbabilityTheory.variance f ρ ≤ (C : ℝ) * ∫ x, ‖gradient f x‖ ^ 2 ∂ρ := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hf2 : MemLp f 2 ρ := hf.continuous.memLp_of_hasCompactSupport hc
  have hd (i : Fin n) : MemLp (coordinateDerivative f i) 2 ρ :=
    (contDiff_coordinateDerivative hf1 (m := 0) (by norm_num) i).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_coordinateDerivative hc i)
  have he := energy_lt_top_of_memLp_coordinateDerivative hd
  have hb := hC f ⟨hf1.locallyLipschitz, hf2⟩
  have ht := ENNReal.toReal_mono
    (ne_of_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top he)) hb
  change ProbabilityTheory.variance f ρ ≤ _ at ht
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, energy_toReal_eq_integral_of_lt_top he] at ht
  exact ht

def affinePoincareLoss (e : Space n ≃ᴬ[ℝ] Space n) : ℝ≥0 :=
  ⟨(‖e.symm.toContinuousAffineMap.contLinear‖ + 1) ^ 2, sq_nonneg _⟩

theorem affinePoincareLoss_pos (e : Space n ≃ᴬ[ℝ] Space n) :
    0 < affinePoincareLoss e := by
  change 0 < (‖e.symm.toContinuousAffineMap.contLinear‖ + 1) ^ 2
  positivity

/-- The actual affine pullback loses a finite, positive operator-norm
factor. Only compact smooth tests are differentiated here. -/
theorem compact_real_poincare_affine_pullback {ρ : Measure (Space n)}
    [IsProbabilityMeasure ρ] (e : Space n ≃ᴬ[ℝ] Space n)
    {C : ℝ≥0} (hC : C ∈ poincareConstants (ρ.map e))
    {f : Space n → ℝ} (hf : ContDiff ℝ 3 f) (hc : HasCompactSupport f) :
    ProbabilityTheory.variance f ρ ≤
      ((C * affinePoincareLoss e : ℝ≥0) : ℝ) * ∫ x, ‖gradient f x‖ ^ 2 ∂ρ := by
  let g : Space n → ℝ := f ∘ e.symm
  have hg : ContDiff ℝ 3 g := hf.comp e.symm.toContinuousAffineMap.contDiff
  have hgc : HasCompactSupport g := hc.comp_homeomorph e.symm.toHomeomorph
  have hvar : ProbabilityTheory.variance g (ρ.map e) = ProbabilityTheory.variance f ρ := by
    rw [ProbabilityTheory.variance_map hg.continuous.measurable.aemeasurable
      e.continuous.measurable.aemeasurable]
    apply ProbabilityTheory.variance_congr
    exact Eventually.of_forall fun x => by simp only [g, Function.comp_apply, e.symm_apply_apply]
  have hG : Integrable (fun y => ‖gradient g y‖ ^ 2) (ρ.map e) :=
    compact_gradient_sq_integrable (hg.of_le (by norm_num)) hgc
  have hGcomp : Integrable (fun x => ‖gradient g (e x)‖ ^ 2) ρ :=
    hG.comp_aemeasurable e.continuous.measurable.aemeasurable
  have hF : Integrable (fun x => ‖gradient f x‖ ^ 2) ρ :=
    compact_gradient_sq_integrable (hf.of_le (by norm_num)) hc
  have hpoint (x : Space n) : ‖gradient g (e x)‖ ^ 2 ≤
      (affinePoincareLoss e : ℝ) * ‖gradient f x‖ ^ 2 := by
    let L : Space n →L[ℝ] Space n := e.symm.toContinuousAffineMap.contLinear
    have hfderiv : HasFDerivAt f (fderiv ℝ f x) (e.symm (e x)) := by
      rw [e.symm_apply_apply]
      exact (hf.differentiable (by norm_num) x).hasFDerivAt
    have hd : HasFDerivAt g ((fderiv ℝ f x).comp L) (e x) :=
      hfderiv.comp (e x) e.symm.toContinuousAffineMap.hasFDerivAt
    have hdf : fderiv ℝ g (e x) = (fderiv ℝ f x).comp L := hd.fderiv
    have hnorm : ‖gradient g (e x)‖ ≤ ‖gradient f x‖ * (‖L‖ + 1) := by
      rw [norm_gradient_eq_norm_fderiv, hdf, norm_gradient_eq_norm_fderiv]
      exact ((fderiv ℝ f x).opNorm_comp_le L).trans
        (mul_le_mul_of_nonneg_left (by linarith : ‖L‖ ≤ ‖L‖ + 1) (norm_nonneg _))
    calc
      _ ≤ (‖gradient f x‖ * (‖L‖ + 1)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = _ := by change _ = (‖L‖ + 1) ^ 2 * _; ring
  have hInt : (∫ y, ‖gradient g y‖ ^ 2 ∂ρ.map e) ≤
      (affinePoincareLoss e : ℝ) * ∫ x, ‖gradient f x‖ ^ 2 ∂ρ := by
    rw [integral_map e.continuous.measurable.aemeasurable hG.aestronglyMeasurable,
      ← integral_const_mul]
    exact integral_mono hGcomp (hF.const_mul _) hpoint
  calc
    _ = ProbabilityTheory.variance g (ρ.map e) := hvar.symm
    _ ≤ (C : ℝ) * ∫ y, ‖gradient g y‖ ^ 2 ∂ρ.map e :=
      compact_real_poincare_of_mem hC hg hgc
    _ ≤ (C : ℝ) * ((affinePoincareLoss e : ℝ) *
        ∫ x, ‖gradient f x‖ ^ 2 ∂ρ) :=
      mul_le_mul_of_nonneg_left hInt C.coe_nonneg
    _ = _ := by simp only [NNReal.coe_mul]; ring

/-- The faithful original test class is recovered by the existing
absolutely-continuous smooth-core theorem, not by a new differentiability
claim about arbitrary transformed locally Lipschitz functions. -/
theorem poincare_mem_affine_pullback {ρ : Measure (Space n)} [IsProbabilityMeasure ρ]
    (hρ : ρ ≪ (volume : Measure (Space n))) (e : Space n ≃ᴬ[ℝ] Space n)
    {C : ℝ≥0} (hCpos : 0 < C) (hC : C ∈ poincareConstants (ρ.map e)) :
    C * affinePoincareLoss e ∈ poincareConstants ρ := by
  apply mem_poincareConstants_of_compact_smooth_tests hρ
    (mul_pos hCpos (affinePoincareLoss_pos e))
  intro f hf hc
  have hgrad : (fun x => ‖gradient f x‖ ^ 2) =
      fun x => ∑ i : Fin n, coordinateDerivative f i x ^ 2 := by
    funext x
    simp_rw [EuclideanSpace.real_norm_sq_eq, coordinateDerivative_eq_gradient]
  have hd (i : Fin n) : MemLp (coordinateDerivative f i) 2 ρ :=
    (contDiff_coordinateDerivative (hf.of_le (by norm_num) : ContDiff ℝ 1 f)
      (m := 0) (by norm_num) i).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_coordinateDerivative hc i)
  have hb := compact_real_poincare_affine_pullback e hC hf hc
  rw [hgrad, integral_finsetSum Finset.univ (fun i _ => (hd i).integrable_sq)] at hb
  exact hb

/-- Each actual canonical source has a finite positive ordinary Poincare
constant. Isotropy is invoked only after actual covariance whitening. -/
theorem exists_source_poincare_constant (d : SourceData μ) (hn : 1 ≤ n) :
    ∃ C : ℝ≥0, 0 < C ∧ C ∈ poincareConstants (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let ν : Measure (Space n) := potentialMeasure d.potential
  letI : IsProbabilityMeasure ν := d.source_probability
  let Q := inverseSqrtMatrix (covarianceMatrix ν)
  let b := -matrixAction Q (∫ x, x ∂ν)
  have hdet : Q.det ≠ 0 := by
    intro hz
    have hw := congrArg Matrix.det
      (inverseSqrtMatrix_mul_self_mul_transpose d.source_covariance_posDef)
    rw [Matrix.det_one] at hw
    change (Q * covarianceMatrix ν * Q.transpose).det = 1 at hw
    simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at hw
    norm_num at hw
  let e := affineMatrixEquiv Q b hdet
  have hmap : ν.map e = whitenedMeasure ν := rfl
  let C₀ : ℝ≥0 := 7004509165936219997049 / 488281250000000000000
  have hC₀pos : 0 < C₀ := by norm_num [C₀]
  have hC₀ : C₀ ∈ poincareConstants (ν.map e) := by
    rw [hmap]
    exact AffineSameTestSeed238452BellmanEndpoint.original_poincare_mem hn
      d.whitened_source_admissible
  have hac : ν ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  exact ⟨C₀ * affinePoincareLoss e, mul_pos hC₀pos (affinePoincareLoss_pos e),
    poincare_mem_affine_pullback (ρ := ν) hac e hC₀pos hC₀⟩

/-- The actual ordinary H1 estimate required for coercivity of each fixed
uniformly elliptic surrogate metric, with the original source weight kept. -/
theorem exists_source_ordinary_H1_poincare (d : SourceData μ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : WeightedCenteredH1 d.potential,
      ‖weightedH1Value d.potential U‖ ^ 2 ≤
        C * ∑ i : Fin n, ‖weightedH1Derivative d.potential i U‖ ^ 2 := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  obtain ⟨C, hCpos, hC⟩ := exists_source_poincare_constant d hn
  refine ⟨C, by exact_mod_cast hCpos, fun U => ?_⟩
  simpa only [weightedEnergyForm_self] using
    weightedH1_bound_of_poincareConstant d.source_C1.continuous hC U

end KLSConstantImprovement.ActualSourceOrdinaryPoincare405

#print axioms KLSConstantImprovement.ActualSourceOrdinaryPoincare405.compact_real_poincare_affine_pullback
#print axioms KLSConstantImprovement.ActualSourceOrdinaryPoincare405.poincare_mem_affine_pullback
#print axioms KLSConstantImprovement.ActualSourceOrdinaryPoincare405.exists_source_poincare_constant
#print axioms KLSConstantImprovement.ActualSourceOrdinaryPoincare405.exists_source_ordinary_H1_poincare

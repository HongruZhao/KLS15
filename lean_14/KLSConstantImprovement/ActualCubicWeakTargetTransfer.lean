import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Portmanteau
import KLS.PairwiseL2
import KLSConstantImprovement.ActualCubicRawMomentTransfer

/-! A raw cubic ProbabilityTheory.variance cap is closed under target weak limits.
The nonnegative pairwise square passes by product Portmanteau, without
convergence of cubic means or squared moments. Actual admissibility,
weak target convergence and the eventual numerical cap are explicit.
No source, derivative, curvature or Poisson fields are passed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace KLSConstantImprovement.ActualCubicWeakTargetTransfer
open KLS KLSBelow25.CubicSymmetricNoise
open ActualDeficitTensorBounds ActualCubicRepresenter ActualCubicRawMomentTransfer
variable {n : ℕ}

theorem evariance_le_of_weak_target_limit
    {μ : ProbabilityMeasure (Space n)} {ν : ℕ → ProbabilityMeasure (Space n)}
    {g : Space n → ℝ} (hg : Continuous g) {B : ℝ≥0∞}
    (hlim : Tendsto ν atTop (𝓝 μ))
    (hbound : ∀ᶠ k in atTop, evariance g (ν k : Measure (Space n)) ≤ B) :
    evariance g (μ : Measure (Space n)) ≤ B := by
  have hp : Tendsto (fun k => (ν k).prod (ν k)) atTop (𝓝 (μ.prod μ)) :=
    (ProbabilityMeasure.continuous_prod.tendsto (μ, μ)).comp (hlim.prodMk_nhds hlim)
  have hc : Continuous (fun z : Space n × Space n => (g z.1-g z.2)^2) :=
    ((hg.comp continuous_fst).sub (hg.comp continuous_snd)).pow 2
  have hn : 0 ≤ (fun z : Space n × Space n => (g z.1-g z.2)^2) :=
    fun z => sq_nonneg _
  have hport := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    hc hn (fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hp hG)
  have hpair : 2 * evariance g (μ : Measure (Space n)) ≤ 2 * B := by
    calc
      _ = ∫⁻ z : Space n × Space n, ENNReal.ofReal ((g z.1-g z.2)^2)
          ∂((μ : Measure (Space n)).prod (μ : Measure (Space n))) :=
        (lintegral_pairwise_sq_eq_two_evariance hg.aestronglyMeasurable).symm
      _ ≤ atTop.liminf (fun k => ∫⁻ z : Space n × Space n,
          ENNReal.ofReal ((g z.1-g z.2)^2)
          ∂((ν k : Measure (Space n)).prod (ν k : Measure (Space n)))) := hport
      _ ≤ 2 * B := by
        apply liminf_le_of_frequently_le'
        apply (hbound.mono ?_).frequently
        intro k hk
        rw [lintegral_pairwise_sq_eq_two_evariance hg.aestronglyMeasurable]
        gcongr
  exact (ENNReal.mul_le_mul_iff_right (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).mp hpair

theorem memLp_and_variance_le_of_weak_target_limit
    {μ : ProbabilityMeasure (Space n)} {ν : ℕ → ProbabilityMeasure (Space n)}
    {g : Space n → ℝ} (hg : Continuous g) {B : ℝ} (hB : 0 ≤ B)
    (hlim : Tendsto ν atTop (𝓝 μ))
    (hν : ∀ k, MemLp g 2 (ν k : Measure (Space n)))
    (hbound : ∀ᶠ k in atTop, ProbabilityTheory.variance g (ν k : Measure (Space n)) ≤ B) :
    MemLp g 2 (μ : Measure (Space n)) ∧ ProbabilityTheory.variance g (μ : Measure (Space n)) ≤ B := by
  have hb : ∀ᶠ k in atTop,
      evariance g (ν k : Measure (Space n)) ≤ ENNReal.ofReal B := by
    filter_upwards [hbound] with k hk
    rw [← ofReal_variance (hν k)]
    exact ENNReal.ofReal_le_ofReal hk
  have he := evariance_le_of_weak_target_limit hg hlim hb
  refine ⟨(evariance_lt_top_iff_memLp hg.aestronglyMeasurable).mp
    (he.trans_lt ENNReal.ofReal_lt_top), ?_⟩
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  simpa only [ProbabilityTheory.variance, ENNReal.toReal_ofReal hB] using hr

theorem actual_cubic_raw_cap_of_weak_target_limit
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {ν : ℕ → Measure (Space n)} (hν : ∀ k, admissibleMeasure (ν k))
    (T : Array3 (Fin n)) {C : ℝ} (hC : 0 ≤ C)
    (hlim : Tendsto (fun k => (@Measure.toProbabilityMeasure (Space n) inferInstance (ν k) (hν k).isProb))
      atTop (𝓝 (@Measure.toProbabilityMeasure (Space n) inferInstance μ hμ.isProb)))
    (hcap : ∀ᶠ k in atTop, ProbabilityTheory.variance (tensorPolynomial (ν k) T) (ν k) ≤ C * tensorSquare T) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ ≤ C * tensorSquare T := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  letI : ∀ k, IsProbabilityMeasure (ν k) := fun k => (hν k).isProb
  have hN : 0 ≤ tensorSquare T := by
    unfold tensorSquare square tripleSum
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb : ∀ᶠ k in atTop, ProbabilityTheory.variance (fixedTensorCubic T) (ν k) ≤ C * tensorSquare T := by
    simpa only [tensorPolynomial_variance_fixed] using hcap
  rw [tensorPolynomial_variance_fixed]
  exact (memLp_and_variance_le_of_weak_target_limit
    (fixedTensorCubic_contDiff T).continuous (mul_nonneg hC hN) hlim
    (fun k => fixedTensorCubic_memLp (hν k) T) hb).2

end KLSConstantImprovement.ActualCubicWeakTargetTransfer
#print axioms KLSConstantImprovement.ActualCubicWeakTargetTransfer.evariance_le_of_weak_target_limit
#print axioms KLSConstantImprovement.ActualCubicWeakTargetTransfer.memLp_and_variance_le_of_weak_target_limit
#print axioms KLSConstantImprovement.ActualCubicWeakTargetTransfer.actual_cubic_raw_cap_of_weak_target_limit

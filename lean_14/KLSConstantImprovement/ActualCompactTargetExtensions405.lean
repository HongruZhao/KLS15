import KLSConstantImprovement.ActualBoundedSourceCalculus
import KLS.WeightedFaithfulCutoff
import KLS.ProbabilityMeanCentering

/-! Original bounded-target polynomial tests have bounded C1 extensions.
The same fixed extension supplies uniformly bounded centered forcing data
on every genuine soft-target approximant. -/
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualCompactTargetExtensions405
open KLS ActualBoundedCanonicalSource
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem exists_compact_C1_target_extension
    {f : Space n → ℝ} (hf : ContDiff ℝ 1 f)
    {K : Set (Space n)} (hK : Bornology.IsBounded K) :
    ∃ (F : Space n → ℝ) (C G : ℝ), ContDiff ℝ 1 F ∧ HasCompactSupport F ∧
      0 ≤ C ∧ 0 ≤ G ∧ (∀ x ∈ K, F x = f x) ∧
      (∀ x, ‖F x‖ ≤ C) ∧ ∀ x, ‖gradient F x‖ ≤ G := by
  obtain ⟨R, hR, hb⟩ := hK.exists_pos_norm_le
  obtain ⟨N, hN⟩ := exists_nat_gt R
  let F : Space n → ℝ := fun x => smoothCutoff n N x * f x
  have hF : ContDiff ℝ 1 F := (smoothCutoff_contDiff N).mul hf
  have hc : HasCompactSupport F := (smoothCutoff_hasCompactSupport N).mul_right
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hF.continuous
  obtain ⟨G, hG⟩ := (hasCompactSupport_gradient hc).exists_bound_of_continuous
    (continuous_gradient_of_contDiff hF)
  refine ⟨F, C, G, hF, hc, (norm_nonneg _).trans (hC 0),
    (norm_nonneg _).trans (hG 0), ?_, hC, hG⟩
  intro x hx
  change smoothCutoff n N x * f x = f x
  rw [smoothCutoff_eq_one_of_norm_le N (by have he := hb x hx; linarith), one_mul]

def centeredTargetDatum (d : SourceData μ) (F : Space n → ℝ) (hF : Continuous F) :
    Lp ℝ 2 (potentialMeasure d.potential) := by
  letI := d.source_probability
  exact CenteredL2.center (potentialMeasure d.potential)
    ((d.continuous_comp_gradient_memLp hF 2).toLp (fun x => F (gradient d.potential x)))

theorem centeredTargetDatum_ae (d : SourceData μ) (F : Space n → ℝ) (hF : Continuous F) :
    (centeredTargetDatum d F hF : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      fun x => F (gradient d.potential x) - ∫ y, F y ∂μ := by
  letI := d.source_probability
  let G : Lp ℝ 2 (potentialMeasure d.potential) :=
    (d.continuous_comp_gradient_memLp hF 2).toLp (fun x => F (gradient d.potential x))
  have hG : (G : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      fun x => F (gradient d.potential x) :=
    (d.continuous_comp_gradient_memLp hF 2).coeFn_toLp
  have hm : (∫ x, G x ∂potentialMeasure d.potential) = ∫ y, F y ∂μ :=
    (integral_congr_ae hG).trans (d.integral_comp_gradient hF)
  filter_upwards [CenteredL2.center_ae (potentialMeasure d.potential) G, hG] with x hx hy
  change CenteredL2.center (potentialMeasure d.potential) G x = _
  rw [hx, hy, hm]

theorem centeredTargetDatum_mean_zero (d : SourceData μ) (F : Space n → ℝ) (hF : Continuous F) :
    (∫ x, centeredTargetDatum d F hF x ∂potentialMeasure d.potential) = 0 := by
  letI := d.source_probability
  exact CenteredL2.integral_center _ _

theorem centeredTargetDatum_norm_le (d : SourceData μ) (F : Space n → ℝ) (hF : Continuous F)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖F x‖ ≤ C) :
    ‖centeredTargetDatum d F hF‖ ≤ C := by
  letI := d.source_probability
  let G : Lp ℝ 2 (potentialMeasure d.potential) :=
    (d.continuous_comp_gradient_memLp hF 2).toLp (fun x => F (gradient d.potential x))
  have hG : (G : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      fun x => F (gradient d.potential x) :=
    (d.continuous_comp_gradient_memLp hF 2).coeFn_toLp
  have hnorm : ‖G‖ ≤ C := by
    apply (sq_le_sq₀ (norm_nonneg G) hC).mp
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    have hi := integral_mono_ae ((Lp.memLp G).integrable_sq)
      (integrable_const (C ^ 2) : Integrable (fun _x : Space n => C ^ 2) (potentialMeasure d.potential))
      (hG.mono fun x hx => by
        change G x ^ 2 ≤ C ^ 2
        rw [hx]
        have h := (sq_le_sq₀ (norm_nonneg (F (gradient d.potential x))) hC).mpr (hb _)
        simpa only [Real.norm_eq_abs, sq_abs] using h)
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hi
    simpa only [RCLike.inner_apply, conj_trivial, ← pow_two] using hi
  exact (CenteredL2.norm_center_le (potentialMeasure d.potential) G).trans hnorm

end KLSConstantImprovement.ActualCompactTargetExtensions405
#print axioms KLSConstantImprovement.ActualCompactTargetExtensions405.exists_compact_C1_target_extension
#print axioms KLSConstantImprovement.ActualCompactTargetExtensions405.centeredTargetDatum_ae
#print axioms KLSConstantImprovement.ActualCompactTargetExtensions405.centeredTargetDatum_mean_zero
#print axioms KLSConstantImprovement.ActualCompactTargetExtensions405.centeredTargetDatum_norm_le

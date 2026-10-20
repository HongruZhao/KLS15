import KLSConstantImprovement.ActualSourceConservativeResolvent405

/-!
The actual BL-defect shifted-filter estimate, proved entirely in the actual
canonical form graph. No spectral-calculus, compact strong-operator core or
free filter bound is assumed. The exact resolvent identity gives contraction
by 1/4 in BL-defect energy; its Cauchy inequality gives the matched 1/2
factor on the same actual source.
-/

noncomputable section
open MeasureTheory InnerProductSpace
open scoped BigOperators ContDiff RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceBLFilter405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualCanonicalMetricResolvent ActualWeakCanonicalMetricInverse
variable {n : ℕ} {μ : Measure (Space n)}

def sourceBLDefect (d : SourceData μ) :
    CanonicalMetricH1 d.potential →L[ℝ] CanonicalMetricH1 d.potential →L[ℝ] ℝ :=
  let valuePair :
      CanonicalMetricH1 d.potential →L[ℝ] CanonicalMetricH1 d.potential →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp (canonicalMetricValue d.potential) (canonicalMetricValue d.potential)
  canonicalMetricEnergy d.potential - valuePair

theorem sourceBLDefect_apply (d : SourceData μ) (U V : CanonicalMetricH1 d.potential) :
    sourceBLDefect d U V = canonicalMetricEnergy d.potential U V -
      inner ℝ (canonicalMetricValue d.potential U) (canonicalMetricValue d.potential V) := by
  simp [sourceBLDefect]

theorem sourceBLDefect_symm (d : SourceData μ) (U V : CanonicalMetricH1 d.potential) :
    sourceBLDefect d U V = sourceBLDefect d V U := by
  rw [sourceBLDefect_apply, sourceBLDefect_apply, canonicalMetricEnergy_symm,
    real_inner_comm (canonicalMetricValue d.potential U)]

theorem sourceBLDefect_nonnegative (d : SourceData μ) (U : CanonicalMetricH1 d.potential) :
    0 ≤ sourceBLDefect d U U := by
  rw [sourceBLDefect_apply, canonicalMetricEnergy_self, real_inner_self_eq_norm_sq]
  exact sub_nonneg.mpr (sourceMetricValue_norm_sq_le_energy d U)

private theorem defect_add_smul_self (d : SourceData μ)
    (U V : CanonicalMetricH1 d.potential) (t : ℝ) :
    sourceBLDefect d (U + t • V) (U + t • V) =
      sourceBLDefect d U U + 2 * t * sourceBLDefect d U V + t ^ 2 * sourceBLDefect d V V := by
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  rw [sourceBLDefect_symm d V U]
  ring

theorem sourceBLDefect_cauchy (d : SourceData μ) (U V : CanonicalMetricH1 d.potential) :
    (sourceBLDefect d U V) ^ 2 ≤ sourceBLDefect d U U * sourceBLDefect d V V := by
  have hp : ∀ t : ℝ, 0 ≤ sourceBLDefect d V V * (t * t) +
      (2 * sourceBLDefect d U V) * t + sourceBLDefect d U U := by
    intro t
    have hn := sourceBLDefect_nonnegative d (U + t • V)
    rw [defect_add_smul_self] at hn
    nlinarith
  have hd := discrim_le_zero hp
  simp only [discrim] at hd
  nlinarith

def formShiftedResolvent (d : SourceData μ) (U : CanonicalMetricH1 d.potential) :
    CanonicalMetricH1 d.potential :=
  canonicalResolventH1 d.potential (t := 1) zero_lt_one (canonicalMetricValue d.potential U)

/-- Exact actual-source relation between the resolvent filter and the BL
defect form; it retains the same scalar generator and mean-zero graph. -/
theorem actual_filter_pairing (d : SourceData μ) (U V : CanonicalMetricH1 d.potential) :
    inner ℝ (canonicalMetricValue d.potential U)
      (canonicalMetricValue d.potential V - (2 : ℝ) •
        canonicalResolvent d.potential (t := 1) zero_lt_one (canonicalMetricValue d.potential V)) =
      sourceBLDefect d U (formShiftedResolvent d V) := by
  have hv := canonicalResolvent_variational d.potential (t := 1) zero_lt_one
    (canonicalMetricValue d.potential V) U
  rw [sourceBLDefect_apply, canonicalMetricEnergy_symm,
    inner_sub_right, inner_smul_right]
  change inner ℝ (canonicalMetricValue d.potential U) (canonicalMetricValue d.potential V) -
    2 * inner ℝ (canonicalMetricValue d.potential U)
      (canonicalMetricValue d.potential (formShiftedResolvent d V)) = _
  change inner ℝ (canonicalMetricValue d.potential (formShiftedResolvent d V))
      (canonicalMetricValue d.potential U) +
    1 * canonicalMetricEnergy d.potential (formShiftedResolvent d V) U =
      inner ℝ (canonicalMetricValue d.potential V) (canonicalMetricValue d.potential U) at hv
  rw [real_inner_comm (canonicalMetricValue d.potential U)
      (canonicalMetricValue d.potential (formShiftedResolvent d V)),
    real_inner_comm (canonicalMetricValue d.potential U) (canonicalMetricValue d.potential V)] at hv
  linarith

/-- Exact defect-energy identity for z=U−2R1U. Its nonnegative right side
proves the sharp 1/4 contraction without any spectral theorem premise. -/
theorem actual_filter_defect_identity (d : SourceData μ) (U : CanonicalMetricH1 d.potential) :
    sourceBLDefect d U U - 4 * sourceBLDefect d (formShiftedResolvent d U) (formShiftedResolvent d U) =
      sourceBLDefect d (U - (2 : ℝ) • formShiftedResolvent d U)
        (U - (2 : ℝ) • formShiftedResolvent d U) +
      4 * ‖canonicalMetricValue d.potential (U - (2 : ℝ) • formShiftedResolvent d U)‖ ^ 2 := by
  let Y := formShiftedResolvent d U
  have hu := canonicalResolvent_variational d.potential (t := 1) zero_lt_one
    (canonicalMetricValue d.potential U) U
  have hy := canonicalResolvent_variational d.potential (t := 1) zero_lt_one
    (canonicalMetricValue d.potential U) Y
  change inner ℝ (canonicalMetricValue d.potential Y) (canonicalMetricValue d.potential U) +
    1 * canonicalMetricEnergy d.potential Y U =
      inner ℝ (canonicalMetricValue d.potential U) (canonicalMetricValue d.potential U) at hu
  rw [real_inner_self_eq_norm_sq] at hu
  change inner ℝ (canonicalMetricValue d.potential Y) (canonicalMetricValue d.potential Y) +
    1 * canonicalMetricEnergy d.potential Y Y =
      inner ℝ (canonicalMetricValue d.potential U) (canonicalMetricValue d.potential Y) at hy
  rw [real_inner_self_eq_norm_sq] at hy
  have he : sourceBLDefect d (U - (2 : ℝ) • Y) (U - (2 : ℝ) • Y) =
      sourceBLDefect d U U - 4 * sourceBLDefect d U Y + 4 * sourceBLDefect d Y Y := by
    have hh := defect_add_smul_self d U Y (-2)
    have hsum : U + (-2 : ℝ) • Y = U - (2 : ℝ) • Y := by
      simp only [neg_smul, sub_eq_add_neg]
    rw [hsum] at hh
    nlinarith
  have hn : ‖canonicalMetricValue d.potential (U - (2 : ℝ) • Y)‖ ^ 2 =
      ‖canonicalMetricValue d.potential U‖ ^ 2 -
        4 * inner ℝ (canonicalMetricValue d.potential U) (canonicalMetricValue d.potential Y) +
        4 * ‖canonicalMetricValue d.potential Y‖ ^ 2 := by
    rw [map_sub, map_smul, norm_sub_sq_real, norm_smul, inner_smul_right]
    norm_num <;> ring
  change sourceBLDefect d U U - 4 * sourceBLDefect d Y Y = _
  rw [he, hn, sourceBLDefect_apply d U Y, sourceBLDefect_apply d Y Y,
    real_inner_self_eq_norm_sq]
  rw [canonicalMetricEnergy_symm d.potential Y U,
    real_inner_comm (canonicalMetricValue d.potential U) (canonicalMetricValue d.potential Y)] at hu
  nlinarith

theorem actual_filter_defect_quarter (d : SourceData μ) (U : CanonicalMetricH1 d.potential) :
    sourceBLDefect d (formShiftedResolvent d U) (formShiftedResolvent d U) ≤
      sourceBLDefect d U U / 4 := by
  have he := actual_filter_defect_identity d U
  have hn := sourceBLDefect_nonnegative d (U - (2 : ℝ) • formShiftedResolvent d U)
  have hs := sq_nonneg ‖canonicalMetricValue d.potential (U - (2 : ℝ) • formShiftedResolvent d U)‖
  linarith

theorem actual_filter_cross_square (d : SourceData μ) (U V : CanonicalMetricH1 d.potential) :
    (inner ℝ (canonicalMetricValue d.potential U)
      (canonicalMetricValue d.potential V - (2 : ℝ) •
        canonicalResolvent d.potential (t := 1) zero_lt_one (canonicalMetricValue d.potential V))) ^ 2 ≤
      sourceBLDefect d U U * sourceBLDefect d V V / 4 := by
  rw [actual_filter_pairing]
  have hc := sourceBLDefect_cauchy d U (formShiftedResolvent d V)
  have hq := mul_le_mul_of_nonneg_left (actual_filter_defect_quarter d V)
    (sourceBLDefect_nonnegative d U)
  nlinarith

/-- The 1/2 matched BL spectral factor is an actual form-resolvent theorem. -/
theorem actual_filter_cross_half (d : SourceData μ) (U V : CanonicalMetricH1 d.potential) :
    |inner ℝ (canonicalMetricValue d.potential U)
      (canonicalMetricValue d.potential V - (2 : ℝ) •
        canonicalResolvent d.potential (t := 1) zero_lt_one (canonicalMetricValue d.potential V))| ≤
      Real.sqrt (sourceBLDefect d U U * sourceBLDefect d V V) / 2 := by
  have hs := actual_filter_cross_square d U V
  have hp := mul_nonneg (sourceBLDefect_nonnegative d U) (sourceBLDefect_nonnegative d V)
  have hr := Real.sq_sqrt hp
  have hn := Real.sqrt_nonneg (sourceBLDefect d U U * sourceBLDefect d V V)
  nlinarith [abs_nonneg (inner ℝ (canonicalMetricValue d.potential U)
    (canonicalMetricValue d.potential V - (2 : ℝ) • canonicalResolvent d.potential (t := 1)
      zero_lt_one (canonicalMetricValue d.potential V))), sq_abs (inner ℝ
        (canonicalMetricValue d.potential U) (canonicalMetricValue d.potential V - (2 : ℝ) •
          canonicalResolvent d.potential (t := 1) zero_lt_one (canonicalMetricValue d.potential V)))]

end KLSConstantImprovement.ActualSourceBLFilter405

#print axioms KLSConstantImprovement.ActualSourceBLFilter405.sourceBLDefect_nonnegative
#print axioms KLSConstantImprovement.ActualSourceBLFilter405.actual_filter_pairing
#print axioms KLSConstantImprovement.ActualSourceBLFilter405.actual_filter_defect_identity
#print axioms KLSConstantImprovement.ActualSourceBLFilter405.actual_filter_cross_half

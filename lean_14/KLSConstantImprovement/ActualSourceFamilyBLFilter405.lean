import KLSConstantImprovement.ActualSourceBLFilter405

/-!
The actual BL-filter half estimate for every finite family of fields in the
same canonical form domain, including all entries of constant normalized
matrix fields. No scalar coefficient/filter premise is assumed.
-/

noncomputable section
open MeasureTheory InnerProductSpace
open scoped BigOperators ContDiff RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceFamilyBLFilter405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualCanonicalMetricResolvent ActualSourceBLFilter405
variable {n : ℕ} {μ : Measure (Space n)} {ι : Type*} [Fintype ι]

private theorem defect_family_cauchy (d : SourceData μ)
    (U V : ι → CanonicalMetricH1 d.potential) :
    (∑ i, sourceBLDefect d (U i) (V i)) ^ 2 ≤
      (∑ i, sourceBLDefect d (U i) (U i)) * (∑ i, sourceBLDefect d (V i) (V i)) := by
  have hp : ∀ t : ℝ, 0 ≤ (∑ i, sourceBLDefect d (V i) (V i)) * (t * t) +
      (2 * ∑ i, sourceBLDefect d (U i) (V i)) * t + ∑ i, sourceBLDefect d (U i) (U i) := by
    intro t
    have hn : 0 ≤ ∑ i, sourceBLDefect d (U i + t • V i) (U i + t • V i) :=
      Finset.sum_nonneg fun i _ => sourceBLDefect_nonnegative d _
    have he (i : ι) : sourceBLDefect d (U i + t • V i) (U i + t • V i) =
        sourceBLDefect d (U i) (U i) + 2 * t * sourceBLDefect d (U i) (V i) +
          t ^ 2 * sourceBLDefect d (V i) (V i) := by
      simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
      rw [sourceBLDefect_symm d (V i) (U i)]
      ring
    simp_rw [he] at hn
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hn
    nlinarith
  have hd := discrim_le_zero hp
  simp only [discrim] at hd
  nlinarith

theorem actual_family_filter_cross_square (d : SourceData μ)
    (U V : ι → CanonicalMetricH1 d.potential) :
    (∑ i, inner ℝ (canonicalMetricValue d.potential (U i))
      (canonicalMetricValue d.potential (V i) - (2 : ℝ) • canonicalResolvent d.potential (t := 1)
        zero_lt_one (canonicalMetricValue d.potential (V i)))) ^ 2 ≤
      (∑ i, sourceBLDefect d (U i) (U i)) *
        (∑ i, sourceBLDefect d (V i) (V i)) / 4 := by
  simp_rw [actual_filter_pairing]
  have hc := defect_family_cauchy d U (fun i => formShiftedResolvent d (V i))
  have hq : (∑ i, sourceBLDefect d (formShiftedResolvent d (V i)) (formShiftedResolvent d (V i))) ≤
      (∑ i, sourceBLDefect d (V i) (V i)) / 4 := by
    have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ => actual_filter_defect_quarter d (V i)
    simpa only [← Finset.sum_div] using hs
  have hU : 0 ≤ ∑ i, sourceBLDefect d (U i) (U i) :=
    Finset.sum_nonneg fun i _ => sourceBLDefect_nonnegative d _
  have hm := mul_le_mul_of_nonneg_left hq hU
  nlinarith

theorem actual_family_filter_cross_half (d : SourceData μ)
    (U V : ι → CanonicalMetricH1 d.potential) :
    |∑ i, inner ℝ (canonicalMetricValue d.potential (U i))
      (canonicalMetricValue d.potential (V i) - (2 : ℝ) • canonicalResolvent d.potential (t := 1)
        zero_lt_one (canonicalMetricValue d.potential (V i)))| ≤
      Real.sqrt ((∑ i, sourceBLDefect d (U i) (U i)) *
        (∑ i, sourceBLDefect d (V i) (V i))) / 2 := by
  have hs := actual_family_filter_cross_square d U V
  have hU : 0 ≤ ∑ i, sourceBLDefect d (U i) (U i) :=
    Finset.sum_nonneg fun i _ => sourceBLDefect_nonnegative d _
  have hV : 0 ≤ ∑ i, sourceBLDefect d (V i) (V i) :=
    Finset.sum_nonneg fun i _ => sourceBLDefect_nonnegative d _
  have hr := Real.sq_sqrt (mul_nonneg hU hV)
  have hn := Real.sqrt_nonneg ((∑ i, sourceBLDefect d (U i) (U i)) *
    (∑ i, sourceBLDefect d (V i) (V i)))
  nlinarith [abs_nonneg (∑ i, inner ℝ (canonicalMetricValue d.potential (U i))
    (canonicalMetricValue d.potential (V i) - (2 : ℝ) • canonicalResolvent d.potential (t := 1)
      zero_lt_one (canonicalMetricValue d.potential (V i)))),
    sq_abs (∑ i, inner ℝ (canonicalMetricValue d.potential (U i))
      (canonicalMetricValue d.potential (V i) - (2 : ℝ) • canonicalResolvent d.potential (t := 1)
        zero_lt_one (canonicalMetricValue d.potential (V i))))]

end KLSConstantImprovement.ActualSourceFamilyBLFilter405

#print axioms KLSConstantImprovement.ActualSourceFamilyBLFilter405.actual_family_filter_cross_square
#print axioms KLSConstantImprovement.ActualSourceFamilyBLFilter405.actual_family_filter_cross_half

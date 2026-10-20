import KLSConstantImprovement.ActualResponseGlobalR1Balance405
import KLSConstantImprovement.ActualSourceResolventForcing405
import KLSConstantImprovement.ActualDirectDeficitBinding405

/-! The literal shifted source moment is the same matched filter cross
already controlled on the actual Hessian/Gram form families. The full
resolvent mean is retained and isotropy pays its trace term. -/
noncomputable section
open MeasureTheory Matrix Filter Set InnerProductSpace
open scoped BigOperators ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualResponseShiftedFilter405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph ActualCanonicalMetricResolvent
open ActualResponseGlobalR1Balance405 ActualSourceMatrixResolvent405 ActualSourceConservativeResolvent405
open ActualSourceResolventForcing405 ActualSourceMatchedDeficit405 ActualSourceTensorGramDefect405
open ActualSourceHessianCongruence405 ActualDirectDeficitBinding405 ActualSourceDirectCubicBalance405
open ActualSourceMeanGram405 ActualSourceDirectCubicEnergy405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
variable {n : ℕ} {μ : Measure (Space n)}

def actualGramEntryLp (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    Lp ℝ 2 (potentialMeasure d.potential) :=
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  ((actual_direct_gram_entry_top d T i j).mono_exponent (by simp)).toLp
    (fun x => matrixTraceGram (coordinateHessian d.potential x) T i j)

theorem actualGramEntryLp_ae (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (actualGramEntryLp d T i j : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      fun x => matrixTraceGram (coordinateHessian d.potential x) T i j := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  exact ((actual_direct_gram_entry_top d T i j).mono_exponent (by simp)).coeFn_toLp

theorem matrix_Lp_inner_trace (d : SourceData μ)
    (A B : Matrix (Fin n) (Fin n) (Lp ℝ 2 (potentialMeasure d.potential)))
    (G : Space n → Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ i j, (B i j : Space n → ℝ) =ᵐ[potentialMeasure d.potential] fun x => G x i j)
    (hG : ∀ᵐ x ∂potentialMeasure d.potential, (G x).IsSymm) :
    (∑ i, ∑ j, inner ℝ (A i j) (B i j)) =
      ∫ x, (matrixFieldValue d A x * G x).trace ∂potentialMeasure d.potential := by
  have hg (i j : Fin n) : MemLp (fun x => G x i j) 2 (potentialMeasure d.potential) :=
    (memLp_congr_ae (hB i j)).mp (Lp.memLp _)
  have hi (i j : Fin n) : Integrable (fun x => A i j x * G x i j) (potentialMeasure d.potential) :=
    (Lp.memLp _).integrable_mul (hg i j)
  have he (i j : Fin n) : inner ℝ (A i j) (B i j) =
      ∫ x, A i j x * G x i j ∂potentialMeasure d.potential := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hB i j] with x hx
    simp only [RCLike.inner_apply, conj_trivial, hx]
    ring
  simp_rw [he]
  have hrow (i : Fin n) : (∑ j, ∫ x, A i j x * G x i j ∂potentialMeasure d.potential) =
      ∫ x, ∑ j, A i j x * G x i j ∂potentialMeasure d.potential :=
    (integral_finsetSum Finset.univ fun j _ => hi i j).symm
  simp_rw [hrow]
  rw [← integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ fun j _ => hi i j)]
  apply integral_congr_ae
  filter_upwards [hG] with x hx
  exact matrix_entrywise_contraction_eq_trace _ _ hx

theorem actual_shifted_moment_filter_identity (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    2 * (∫ x, actualResponseShiftedMoment d T x ∂potentialMeasure d.potential) =
      (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) + (sourceMeanGram d T).trace -
        actualMatrixFilterCross d 1 T := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let F := sourceHessianLp d
  let G : Matrix (Fin n) (Fin n) (Lp ℝ 2 (potentialMeasure d.potential)) := Matrix.of (actualGramEntryLp d T)
  have hF (i j : Fin n) : (F i j : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      fun x => coordinateHessian d.potential x i j := (d.hessian_entry_memLp i j 2).coeFn_toLp
  have hG (i j : Fin n) : (G i j : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      fun x => matrixTraceGram (coordinateHessian d.potential x) T i j := actualGramEntryLp_ae d T i j
  have hmF (i j : Fin n) : (∫ x, F i j x ∂potentialMeasure d.potential) =
      (1 : Matrix (Fin n) (Fin n) ℝ) i j := (integral_congr_ae (hF i j)).trans (d.hessian_entry_mean_eq_one hiso i j)
  have hmG (i j : Fin n) : (∫ x, G i j x ∂potentialMeasure d.potential) = sourceMeanGram d T i j :=
    integral_congr_ae (hG i j)
  have hUc (i j : Fin n) : canonicalMetricValue d.potential (actualHessianCongruenceForm d 1 i j) =
      CenteredL2.center (potentialMeasure d.potential) (F i j) := by
    apply Lp.ext
    have hm := integral_congr_ae (hF i j)
    filter_upwards [actual_base_hessian_value_ae d i j, CenteredL2.center_ae (potentialMeasure d.potential) (F i j), hF i j] with x hv hc hf
    rw [hc, hf, hm]
    exact hv
  have hVc (i j : Fin n) : canonicalMetricValue d.potential (actualTensorGramForm d T i j) =
      CenteredL2.center (potentialMeasure d.potential) (G i j) := by
    have hv : (canonicalMetricValue d.potential (actualTensorGramForm d T i j) : Space n → ℝ)
        =ᵐ[potentialMeasure d.potential] fun x => matrixTraceGram (coordinateHessian d.potential x) T i j - sourceMeanGram d T i j := by
      simpa only [sourceTensorGramEntry_eq_matrixTraceGram, sourceMeanGram] using actualTensorGramForm_value_ae d T i j
    apply Lp.ext
    filter_upwards [hv, CenteredL2.center_ae (potentialMeasure d.potential) (G i j), hG i j] with x hv' hc hg
    rw [hc, hg, hmG]
    exact hv'
  have hentry (i j : Fin n) :
      2 * inner ℝ (sourceConservativeResolvent d (t := 1) zero_lt_one (F i j)) (G i j) =
        inner ℝ (F i j) (G i j) + (1 : Matrix (Fin n) (Fin n) ℝ) i j * sourceMeanGram d T i j -
          inner ℝ (canonicalMetricValue d.potential (actualHessianCongruenceForm d 1 i j))
            (canonicalMetricValue d.potential (actualTensorGramForm d T i j) - (2 : ℝ) •
              canonicalResolvent d.potential (t := 1) zero_lt_one
                (canonicalMetricValue d.potential (actualTensorGramForm d T i j))) := by
    have he := actual_full_resolvent_forcing_identity d (F i j) (G i j)
    rw [hmF, hmG, ← hUc, ← hVc] at he
    exact he
  have hsum : (∑ i, ∑ j, 2 * inner ℝ (sourceConservativeResolvent d (t := 1) zero_lt_one (F i j)) (G i j)) =
      ∑ i, ∑ j, (inner ℝ (F i j) (G i j) + (1 : Matrix (Fin n) (Fin n) ℝ) i j * sourceMeanGram d T i j -
        inner ℝ (canonicalMetricValue d.potential (actualHessianCongruenceForm d 1 i j))
          (canonicalMetricValue d.potential (actualTensorGramForm d T i j) - (2 : ℝ) •
            canonicalResolvent d.potential (t := 1) zero_lt_one (canonicalMetricValue d.potential (actualTensorGramForm d T i j)))) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hentry i j
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  have hGsym : ∀ᵐ x ∂potentialMeasure d.potential, (matrixTraceGram (coordinateHessian d.potential x) T).IsSymm :=
    Eventually.of_forall fun x => matrixTraceGram_symmetric _ T
  have hR := matrix_Lp_inner_trace d (sourceMatrixResolvent d F) G
    (fun x => matrixTraceGram (coordinateHessian d.potential x) T) hG hGsym
  have hHG : (∑ i, ∑ j, inner ℝ (F i j) (G i j)) =
      ∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential := by
    rw [matrix_Lp_inner_trace d F G (fun x => matrixTraceGram (coordinateHessian d.potential x) T) hG hGsym]
    apply integral_congr_ae
    filter_upwards [sourceHessianLp_ae d] with x hx
    change (matrixFieldValue d (sourceHessianLp d) x *
      matrixTraceGram (coordinateHessian d.potential x) T).trace = actualDirectMoment d T x
    rw [hx]
    rfl
  have hm : (∑ i, ∑ j, (1 : Matrix (Fin n) (Fin n) ℝ) i j * sourceMeanGram d T i j) =
      (sourceMeanGram d T).trace := by simp [Matrix.one_apply, Matrix.trace]
  change (∑ i, ∑ j, inner ℝ (sourceConservativeResolvent d (t := 1) zero_lt_one (F i j)) (G i j)) =
    ∫ x, actualResponseShiftedMoment d T x ∂potentialMeasure d.potential at hR
  rw [hR, hHG, hm] at hsum
  exact hsum

end KLSConstantImprovement.ActualResponseShiftedFilter405

#print axioms KLSConstantImprovement.ActualResponseShiftedFilter405.matrix_Lp_inner_trace
#print axioms KLSConstantImprovement.ActualResponseShiftedFilter405.actual_shifted_moment_filter_identity

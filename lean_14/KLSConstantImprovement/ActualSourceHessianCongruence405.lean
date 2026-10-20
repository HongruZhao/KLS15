import KLSConstantImprovement.ActualSourceHessianFormEquation405
import KLSConstantImprovement.ActualSourceBLFilter405
import KLS.WeakHessianVariance

/-! Every fixed congruence of the actual C1,1 source Hessian belongs to
the same closed scalar form. Its total BL defect is paid by the literal
trace-square deficit. No congruence field, weak derivative, energy domain,
or matrix variance certificate is supplied as an analytic hypothesis. -/
noncomputable section
open MeasureTheory Matrix Set Filter InnerProductSpace ProbabilityTheory
open scoped BigOperators ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceHessianCongruence405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualCompactRawMetricGraph ActualBoundedRawMetricDomain ActualSourceBLFilter405
open ActualSourceHessianEvolution405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

private theorem source_third_slices_symmetric (d : SourceData μ) :
    ∀ᵐ x ∂(volume : Measure (Space n)), ∀ k, (sourceThirdMatrix d x k).IsSymm := by
  filter_upwards [d.third_symmetric_ae] with x hx
  exact fun k => Matrix.IsSymm.ext (fun i j => (hx k j i).2)

private theorem transpose_mul_self_positive (R : Matrix (Fin n) (Fin n) ℝ) :
    (R.transpose * R).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_one] using
    (Matrix.PosSemidef.one : (1 : Matrix (Fin n) (Fin n) ℝ).PosSemidef).conjTranspose_mul_mul_same R

theorem exists_actual_hessian_congruence_form (d : SourceData μ)
    (R : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) :
    ∃ U : CanonicalMetricH1 d.potential,
      (canonicalMetricValue d.potential U : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
        (fun x => hessianCongruence d.potential R x a b -
          ∫ y, hessianCongruence d.potential R y a b ∂potentialMeasure d.potential) ∧
      ∀ i, (canonicalMetricGradient d.potential i U : Space n → ℝ)
        =ᵐ[potentialMeasure d.potential] rawCanonicalMetricDerivative d.potential
          (fun k y => (R * sourceThirdMatrix d y k * R.transpose) a b) i := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hA := (d.global_trace_energy (transpose_mul_self_positive R)).2.1
  apply d.bounded_raw_metric_pair_mem
    (memLp_hessianCongruence_entry_C11 d.gradient_lipschitz R a b).aestronglyMeasurable
    (fun x => matrix_congruence_entry_bound_raw (coordinateHessian d.potential x) R
      (fun i j => actual_hessian_global_entry_bound d.gradient_lipschitz x i j) a b)
    (fun k E hE => memLp_two_matrixCongruence_raw
      (fun i j => d.third_local_L2 k i j E hE) R a b)
    (fun k => hasLocalWeakCoordinateDerivative_actual_hessianCongruence
      d.gradient_lipschitz.locallyLipschitz d.third_local_L2 d.third_weak_derivative R k a b)
    (integrable_raw_hessianCongruence_energy (d.hessian_ae.mono fun _ hx => hx.1)
      d.third_local_L2 (source_third_slices_symmetric d) R hA a b)

def actualHessianCongruenceForm (d : SourceData μ)
    (R : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) : CanonicalMetricH1 d.potential :=
  Classical.choose (exists_actual_hessian_congruence_form d R a b)

theorem actualHessianCongruenceForm_value_ae (d : SourceData μ)
    (R : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) :
    (canonicalMetricValue d.potential (actualHessianCongruenceForm d R a b) : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential] (fun x => hessianCongruence d.potential R x a b -
        ∫ y, hessianCongruence d.potential R y a b ∂potentialMeasure d.potential) :=
  (Classical.choose_spec (exists_actual_hessian_congruence_form d R a b)).1

theorem actualHessianCongruenceForm_gradient_ae (d : SourceData μ)
    (R : Matrix (Fin n) (Fin n) ℝ) (a b i : Fin n) :
    (canonicalMetricGradient d.potential i (actualHessianCongruenceForm d R a b) : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential] rawCanonicalMetricDerivative d.potential
        (fun k y => (R * sourceThirdMatrix d y k * R.transpose) a b) i :=
  (Classical.choose_spec (exists_actual_hessian_congruence_form d R a b)).2 i

theorem actual_raw_form_self_energy (d : SourceData μ)
    (U : CanonicalMetricH1 d.potential) (F : Fin n → Space n → ℝ)
    (hU : ∀ i, (canonicalMetricGradient d.potential i U : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential] rawCanonicalMetricDerivative d.potential F i) :
    canonicalMetricEnergy d.potential U U =
      ∫ x, rawInverseHessianGradientForm d.potential F x ∂potentialMeasure d.potential := by
  have hF (i : Fin n) : MemLp (rawCanonicalMetricDerivative d.potential F i) 2
      (potentialMeasure d.potential) :=
    (memLp_congr_ae (hU i)).mp (Lp.memLp (canonicalMetricGradient d.potential i U))
  have he (i : Fin n) : inner ℝ (canonicalMetricGradient d.potential i U)
      (canonicalMetricGradient d.potential i U) = ∫ x,
        rawCanonicalMetricDerivative d.potential F i x ^ 2 ∂potentialMeasure d.potential := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hU i] with x hx
    simp only [RCLike.inner_apply, conj_trivial, hx, pow_two]
  rw [canonicalMetricEnergy_apply]
  simp_rw [he]
  rw [← integral_finsetSum Finset.univ (fun i _ => (hF i).integrable_sq)]
  exact integral_congr_ae (d.raw_metric_derivative_sq_ae F)

theorem actual_hessian_congruence_total_energy (d : SourceData μ)
    (R : Matrix (Fin n) (Fin n) ℝ) :
    (∑ a, ∑ b, canonicalMetricEnergy d.potential
      (actualHessianCongruenceForm d R a b) (actualHessianCongruenceForm d R a b)) =
      ∫ x, rawHessianTraceGradientTerm (coordinateHessian d.potential x)
        (R.transpose * R) (sourceThirdMatrix d x) ∂potentialMeasure d.potential := by
  simp_rw [actual_raw_form_self_energy d _ _ (actualHessianCongruenceForm_gradient_ae d R _ _)]
  exact sum_integral_raw_energy_hessianCongruence (d.hessian_ae.mono fun _ hx => hx.1)
    d.third_local_L2 (source_third_slices_symmetric d) R
    (d.global_trace_energy (transpose_mul_self_positive R)).2.1

theorem actual_hessian_congruence_total_variance (d : SourceData μ)
    (hiso : IsIsotropic μ) (R : Matrix (Fin n) (Fin n) ℝ) :
    (∑ a, ∑ b, ‖canonicalMetricValue d.potential (actualHessianCongruenceForm d R a b)‖ ^ 2) =
      (∫ x, rawHessianTraceSquare (coordinateHessian d.potential x) (R.transpose * R)
        ∂potentialMeasure d.potential) - ((R.transpose * R) * (R.transpose * R)).trace := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have he (a b : Fin n) :
      ‖canonicalMetricValue d.potential (actualHessianCongruenceForm d R a b)‖ ^ 2 =
        variance (fun x => hessianCongruence d.potential R x a b) (potentialMeasure d.potential) := by
    rw [ProbabilityTheory.variance_eq_integral
      (memLp_hessianCongruence_entry_C11 d.gradient_lipschitz R a b).aemeasurable,
      ← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [actualHessianCongruenceForm_value_ae d R a b] with x hx
    simp only [RCLike.inner_apply, conj_trivial, hx, pow_two]
  simp_rw [he]
  exact sum_variance_hessianCongruence_C11 d.source_C1 d.gradient_lipschitz
    (d.pushforward.symm ▸ hiso) R

theorem actual_hessian_congruence_BL_deficit (d : SourceData μ)
    (hiso : IsIsotropic μ) (R : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ (∑ a, ∑ b, sourceBLDefect d
      (actualHessianCongruenceForm d R a b) (actualHessianCongruenceForm d R a b)) ∧
    (∑ a, ∑ b, sourceBLDefect d
      (actualHessianCongruenceForm d R a b) (actualHessianCongruenceForm d R a b)) ≤
        ((R.transpose * R) * (R.transpose * R)).trace - (1/2 : ℝ) *
          ∫ x, rawHessianTraceSquare (coordinateHessian d.potential x) (R.transpose * R)
            ∂potentialMeasure d.potential := by
  constructor
  · exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
      sourceBLDefect_nonnegative d _
  · have hhalf := (d.global_trace_energy (transpose_mul_self_positive R)).2.2.2.2.2
    change (∫ x, rawHessianTraceGradientTerm (coordinateHessian d.potential x)
      (R.transpose * R) (sourceThirdMatrix d x) ∂potentialMeasure d.potential) ≤
        (1 / 2 : ℝ) * ∫ x, rawHessianTraceSquare (coordinateHessian d.potential x)
          (R.transpose * R) ∂potentialMeasure d.potential at hhalf
    simp only [sourceBLDefect_apply, real_inner_self_eq_norm_sq, Finset.sum_sub_distrib]
    rw [actual_hessian_congruence_total_energy, actual_hessian_congruence_total_variance d hiso]
    linarith

end KLSConstantImprovement.ActualSourceHessianCongruence405
#print axioms KLSConstantImprovement.ActualSourceHessianCongruence405.exists_actual_hessian_congruence_form
#print axioms KLSConstantImprovement.ActualSourceHessianCongruence405.actual_hessian_congruence_total_energy
#print axioms KLSConstantImprovement.ActualSourceHessianCongruence405.actual_hessian_congruence_total_variance
#print axioms KLSConstantImprovement.ActualSourceHessianCongruence405.actual_hessian_congruence_BL_deficit

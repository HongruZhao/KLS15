import KLSConstantImprovement.ActualWeakCanonicalMetricOrdinaryGraph

/-!
The constructed canonical inverse-Hessian form is a form on scalar L2
functions: its value projection is injective. This is proved from actual
weak differentiation, ordinary graph closability, and AE invertibility of
the actual root. A free metric closability or operator-domain certificate
is not supplied as an input.
-/

noncomputable section
open MeasureTheory InnerProductSpace Matrix Filter
open scoped BigOperators ContDiff RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceMetricFaithfulness405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualWeakCanonicalMetricOrdinaryGraph
variable {n : ℕ} {μ : Measure (Space n)}

theorem canonicalMetricRoot_mul_unroot_at {φ : Space n → ℝ} {x : Space n}
    (hpos : (coordinateHessian φ x).PosDef) :
    canonicalMetricRoot φ x * canonicalMetricUnroot φ x = 1 := by
  exact Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (canonicalMetricRoot_posDef_at hpos).isUnit)

/-- The ordinary weak derivative of a metric graph value is the actual
positive Hessian root applied to its actual metric-gradient coordinates. -/
theorem sourceOrdinaryH1Embedding_derivative_ae (d : SourceData μ)
    (U : CanonicalMetricH1 d.potential) (i : Fin n) :
    (weightedH1Derivative d.potential i (sourceOrdinaryH1Embedding d U) : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential] fun x =>
        ∑ j : Fin n, canonicalMetricUnroot d.potential x i j *
          canonicalMetricGradient d.potential j U x := by
  rw [sourceOrdinaryH1Embedding_derivative]
  have hmul : ∀ᵐ x ∂potentialMeasure d.potential, ∀ j : Fin n,
      sourceUnrootMultiplier d i j (canonicalMetricGradient d.potential j U) x =
        canonicalMetricUnroot d.potential x i j * canonicalMetricGradient d.potential j U x :=
    ae_all_iff.mpr fun j => sourceUnrootMultiplier_coe d i j _
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j : Fin n =>
    sourceUnrootMultiplier d i j (canonicalMetricGradient d.potential j U)), hmul]
    with x hx hm
  rw [hx]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => hm j

theorem metricGradient_eq_zero_of_value_eq_zero (d : SourceData μ)
    {U : CanonicalMetricH1 d.potential} (hU : canonicalMetricValue d.potential U = 0)
    (i : Fin n) : canonicalMetricGradient d.potential i U = 0 := by
  have hemb : sourceOrdinaryH1Embedding d U = 0 := by
    apply weightedH1_eq_zero_of_value_eq_zero d.source_C1
    rw [sourceOrdinaryH1Embedding_value, hU]
  have hd (j : Fin n) :
      weightedH1Derivative d.potential j (sourceOrdinaryH1Embedding d U) = 0 := by
    rw [hemb, map_zero]
  have hpoint (j : Fin n) : ∀ᵐ x ∂potentialMeasure d.potential,
      ∑ k : Fin n, canonicalMetricUnroot d.potential x j k *
        canonicalMetricGradient d.potential k U x = 0 := by
    have hz : (weightedH1Derivative d.potential j (sourceOrdinaryH1Embedding d U) : Space n → ℝ)
        =ᵐ[potentialMeasure d.potential] fun _ => 0 := by
      rw [hd j]
      exact Lp.coeFn_zero ℝ 2 (potentialMeasure d.potential)
    exact (sourceOrdinaryH1Embedding_derivative_ae d U j).symm.trans hz
  have hp : (canonicalMetricGradient d.potential i U : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential] fun _ => 0 := by
    filter_upwards [ae_all_iff.mpr hpoint, d.hessian_ae_source] with x hx hpos
    let p : Fin n → ℝ := fun k => canonicalMetricGradient d.potential k U x
    have hmul : canonicalMetricUnroot d.potential x *ᵥ p = 0 := funext hx
    have hz : p = 0 := by
      calc
        p = canonicalMetricRoot d.potential x *ᵥ
            (canonicalMetricUnroot d.potential x *ᵥ p) := by
          rw [Matrix.mulVec_mulVec, canonicalMetricRoot_mul_unroot_at hpos.1, Matrix.one_mulVec]
        _ = 0 := by rw [hmul, Matrix.mulVec_zero]
    exact congrFun hz i
  apply Lp.ext
  exact hp.trans (Lp.coeFn_zero ℝ 2 (potentialMeasure d.potential)).symm

/-- Actual scalar values determine the completed canonical metric graph. -/
theorem metricH1_eq_zero_of_value_eq_zero (d : SourceData μ)
    {U : CanonicalMetricH1 d.potential} (hU : canonicalMetricValue d.potential U = 0) : U = 0 := by
  have hn := canonicalMetricH1_norm_sq d.potential U
  have hd := metricGradient_eq_zero_of_value_eq_zero d hU
  simp only [hU, hd, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    Finset.sum_const_zero, add_zero] at hn
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg U])

theorem canonicalMetricValue_injective (d : SourceData μ) :
    Function.Injective (canonicalMetricValue d.potential) := by
  intro U V huv
  apply sub_eq_zero.mp
  apply metricH1_eq_zero_of_value_eq_zero d
  rw [map_sub, huv, sub_self]

end KLSConstantImprovement.ActualSourceMetricFaithfulness405

#print axioms KLSConstantImprovement.ActualSourceMetricFaithfulness405.sourceOrdinaryH1Embedding_derivative_ae
#print axioms KLSConstantImprovement.ActualSourceMetricFaithfulness405.metricGradient_eq_zero_of_value_eq_zero
#print axioms KLSConstantImprovement.ActualSourceMetricFaithfulness405.canonicalMetricValue_injective

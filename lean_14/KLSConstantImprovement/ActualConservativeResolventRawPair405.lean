import KLSConstantImprovement.ActualHessianResolventRawTests405
import KLSConstantImprovement.ActualWeakCanonicalMetricInverse

/-! The actual full unit resolvent pairs with an uncentered raw test
through the exact natural form of its centered value. Its mean term is
removed using the proved conservative resolvent mean identity. -/
noncomputable section
open MeasureTheory InnerProductSpace Filter
open scoped BigOperators RealInnerProductSpace
namespace KLSConstantImprovement.ActualConservativeResolventRawPair405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph ActualCanonicalMetricResolvent
open ActualWeakCanonicalMetricInverse ActualSourceConservativeResolvent405 ActualSourceResolventPoisson405
open ActualHessianResolventRawTests405 ActualSourceMatrixResolvent405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {n : ℕ} {μ : Measure (Space n)}

theorem unit_resolvent_raw_form_pair (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (f : Space n → ℝ)
    (hf : MemLp f 2 (potentialMeasure d.potential)) (V : CanonicalMetricH1 d.potential)
    (hv : (canonicalMetricValue d.potential V : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      fun x => f x - ∫ y, f y ∂potentialMeasure d.potential) :
    canonicalMetricEnergy d.potential (canonicalResolventH1 d.potential (t := 1) zero_lt_one g) V =
      ∫ x, (g x - sourceConservativeResolvent d (t := 1) zero_lt_one g x) * f x
        ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let F := g - sourceConservativeResolvent d (t := 1) zero_lt_one g
  let flp : Lp ℝ 2 (potentialMeasure d.potential) := hf.toLp f
  have hfcoe : (flp : Space n → ℝ) =ᵐ[potentialMeasure d.potential] f := hf.coeFn_toLp
  have hmean : (∫ x, flp x ∂potentialMeasure d.potential) = ∫ x, f x ∂potentialMeasure d.potential :=
    integral_congr_ae hfcoe
  have hval : canonicalMetricValue d.potential V = CenteredL2.center (potentialMeasure d.potential) flp := by
    apply Lp.ext
    filter_upwards [hv, CenteredL2.center_ae (potentialMeasure d.potential) flp, hfcoe] with x hx hc hf'
    rw [hc, hf', hmean]
    exact hx
  have hFmean : (∫ x, F x ∂potentialMeasure d.potential) = 0 := sourceResolventForcing_integral_zero d g
  have hone : inner ℝ F (CenteredL2.oneLp (potentialMeasure d.potential)) = 0 := by
    rw [real_inner_comm, CenteredL2.inner_oneLp]
    exact hFmean
  rw [sourceResolventH1_eq_inverse_forcing, sourceMetricInverse_variational]
  change inner ℝ F (canonicalMetricValue d.potential V) = _
  rw [hval, CenteredL2.center, inner_sub_right, inner_smul_right, hone, mul_zero, sub_zero, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub g (sourceConservativeResolvent d (t := 1) zero_lt_one g), hfcoe] with x hx hfl
  simp only [RCLike.inner_apply, conj_trivial, F, hx, Pi.sub_apply, hfl]
  ring

theorem actual_hessian_resolvent_form_raw_pair (d : SourceData μ) (i j : Fin n)
    (f : Space n → ℝ) (hf : MemLp f 2 (potentialMeasure d.potential)) (V : CanonicalMetricH1 d.potential)
    (hv : (canonicalMetricValue d.potential V : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      fun x => f x - ∫ y, f y ∂potentialMeasure d.potential) :
    canonicalMetricEnergy d.potential (actualHessianResolventForm d i j) V =
      ∫ x, (coordinateHessian d.potential x i j - sourceMatrixResolvent d (sourceHessianLp d) i j x) * f x
        ∂potentialMeasure d.potential := by
  calc
    _ = ∫ x, (sourceHessianLp d i j x - sourceConservativeResolvent d (t := 1) zero_lt_one
        (sourceHessianLp d i j) x) * f x ∂potentialMeasure d.potential :=
      unit_resolvent_raw_form_pair d (sourceHessianLp d i j) f hf V hv
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [sourceHessianLp_ae d] with x hx
      have hij := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) hx
      change sourceHessianLp d i j x = coordinateHessian d.potential x i j at hij
      change (sourceHessianLp d i j x - _) * f x = _
      rw [hij]
      rfl

end KLSConstantImprovement.ActualConservativeResolventRawPair405

#print axioms KLSConstantImprovement.ActualConservativeResolventRawPair405.unit_resolvent_raw_form_pair
#print axioms KLSConstantImprovement.ActualConservativeResolventRawPair405.actual_hessian_resolvent_form_raw_pair

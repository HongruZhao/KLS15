import KLSConstantImprovement.ActualResponseIntegralEnergy405
import KLSConstantImprovement.ActualQuarticHessianTest405
import KLSConstantImprovement.ActualBoundedRawSourceCalculus405

/-! Literal trace-response vector for the same actual source. Its bounded
weak test, genuine weak derivative and global ordinary L2 derivative are
constructed; its scalar response uses the actual canonical variational inverse. -/
noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators
namespace KLSConstantImprovement.ActualTraceResponse405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualBoundedRawTestAlgebra405 ActualQuarticHessianTest405
open ActualBoundedRawSourceCalculus405 ActualResponseIntegralEnergy405
open ActualWeakCanonicalMetricResponse
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

def actualTraceField (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (x : Space n) : ℝ :=
  (T i * (coordinateHessian d.potential x - 1)).trace

def traceResponseTest (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : BoundedRawTest d :=
  rawTestSum fun a : Fin n => rawTestSum fun b : Fin n =>
    (BoundedRawTest.const d (T i a b)).mul
      ((BoundedRawTest.hessian d b a).add
        (BoundedRawTest.const d (-(1 : Matrix (Fin n) (Fin n) ℝ) b a)))

theorem traceResponseTest_value (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (x : Space n) :
    (traceResponseTest d T i).value x = actualTraceField d T i x := by
  change (∑ a, ∑ b, T i a b * (coordinateHessian d.potential x b a +
    -(1 : Matrix (Fin n) (Fin n) ℝ) b a)) = _
  simp only [actualTraceField, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    sub_eq_add_neg, Matrix.add_apply, Matrix.neg_apply]

theorem traceResponseTest_derivative (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i c : Fin n) (x : Space n) :
    (traceResponseTest d T i).derivative c x =
      ∑ a, ∑ b, T i a b * d.third x c b a := by
  simp only [traceResponseTest, rawTestSum, BoundedRawTest.mul, BoundedRawTest.add,
    BoundedRawTest.const, BoundedRawTest.hessian, mul_zero, zero_mul, add_zero, zero_add]

theorem actualTraceField_memLp (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    MemLp (actualTraceField d T i) 2 (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have he : (traceResponseTest d T i).value = actualTraceField d T i := funext (traceResponseTest_value d T i)
  rw [← he]
  exact (traceResponseTest d T i).value_top.mono_exponent (by simp)

def actualTraceVector (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : Lp ℝ 2 (potentialMeasure d.potential) :=
  (actualTraceField_memLp d T i).toLp (actualTraceField d T i)

theorem actualTraceVector_coe (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (actualTraceVector d T i : Space n → ℝ) =ᵐ[potentialMeasure d.potential] actualTraceField d T i :=
  (actualTraceField_memLp d T i).coeFn_toLp

theorem actual_trace_derivative_memLp (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i c : Fin n) :
    MemLp (fun x => ∑ a, ∑ b, T i a b * d.third x c b a) 2 (potentialMeasure d.potential) := by
  have he : (traceResponseTest d T i).derivative c =
      fun x => ∑ a, ∑ b, T i a b * d.third x c b a :=
    funext (traceResponseTest_derivative d T i c)
  rw [← he]
  exact ActualBoundedRawSourceCalculus405.BoundedRawTest.ordinary_derivative_memLp _ _

def actualTraceResponse (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) : Lp ℝ 2 (potentialMeasure d.potential) :=
  sourceResponse d (actualTraceVector d T)

theorem actual_trace_response_H_energy_cap (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    ‖actualTraceResponse d T‖ ^ 2 ≤
      ∫ x, ∑ a, ∑ b, coordinateHessian d.potential x a b *
        actualTraceField d T a x * actualTraceField d T b x ∂potentialMeasure d.potential := by
  have hb := actual_response_norm_le_H_energy d (actualTraceVector d T)
  change ‖actualTraceResponse d T‖ ^ 2 ≤ _ at hb
  have he : (∫ x, ∑ a, ∑ b, coordinateHessian d.potential x a b *
      actualTraceVector d T a x * actualTraceVector d T b x ∂potentialMeasure d.potential) =
      ∫ x, ∑ a, ∑ b, coordinateHessian d.potential x a b *
        actualTraceField d T a x * actualTraceField d T b x ∂potentialMeasure d.potential := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (actualTraceVector_coe d T)] with x hx
    simp only [hx]
  exact he ▸ hb

end KLSConstantImprovement.ActualTraceResponse405
#print axioms KLSConstantImprovement.ActualTraceResponse405.traceResponseTest_derivative
#print axioms KLSConstantImprovement.ActualTraceResponse405.actualTraceField_memLp
#print axioms KLSConstantImprovement.ActualTraceResponse405.actual_trace_derivative_memLp
#print axioms KLSConstantImprovement.ActualTraceResponse405.actual_trace_response_H_energy_cap

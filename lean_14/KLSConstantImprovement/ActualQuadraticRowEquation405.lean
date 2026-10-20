import KLSConstantImprovement.ActualNaturalFluxRowEquation405
import KLSConstantImprovement.ActualAffineMatrixTests405

/-! Literal quadratic data and their differentiated natural Poisson rows.
All weak derivatives are constructed from the actual bounded source
coordinate algebra, and the Jacobian is the actual Gaffney choice. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators ENNReal ContDiff
namespace KLSConstantImprovement.ActualQuadraticRowEquation405
open KLS ActualBoundedCanonicalSource ActualSourceNaturalGaffney405 ActualSourceQuadraticEta405
open ActualBoundedRawTestAlgebra405 ActualQuarticHessianTest405 ActualBoundedRawSourceCalculus405
open ActualQuadraticResponseField405 ActualNaturalFluxRowEquation405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {n : ℕ} {μ : Measure (Space n)}

def halfQuadraticRawTest (d : SourceData μ) (B : Matrix (Fin n) (Fin n) ℝ) : BoundedRawTest d :=
  (rawTestSum fun a : Fin n => rawTestSum fun b : Fin n =>
    (BoundedRawTest.const d (B a b / 2)).mul
      ((ActualBoundedRawSourceCalculus405.BoundedRawTest.coordinate d a).mul
        (ActualBoundedRawSourceCalculus405.BoundedRawTest.coordinate d b))).add
    (BoundedRawTest.const d (-B.trace / 2))

def quadraticDatumRawDerivative (d : SourceData μ) (B : Matrix (Fin n) (Fin n) ℝ)
    (j : Fin n) (x : Space n) : ℝ :=
  ∑ a : Fin n, ∑ b : Fin n, (B a b / 2) *
    (coordinateHessian d.potential x j a * gradient d.potential x b +
      gradient d.potential x a * coordinateHessian d.potential x j b)

theorem halfQuadraticRawTest_value (d : SourceData μ) (B : Matrix (Fin n) (Fin n) ℝ)
    (x : Space n) :
    (halfQuadraticRawTest d B).value x =
      ActualCubicGradientEnergy.centeredQuadratic B (gradient d.potential x) / 2 := by
  change (∑ a : Fin n, ∑ b : Fin n, (B a b / 2) *
      (gradient d.potential x a * gradient d.potential x b)) + (-B.trace / 2) = _
  have he (a b : Fin n) : (B a b / 2) * (gradient d.potential x a * gradient d.potential x b) =
      (B a b * gradient d.potential x a * gradient d.potential x b) / 2 := by ring
  simp_rw [he]
  simp only [← Finset.sum_div, ActualCubicGradientEnergy.centeredQuadratic, matrixQuadratic]
  ring

theorem halfQuadraticRawTest_derivative (d : SourceData μ) (B : Matrix (Fin n) (Fin n) ℝ)
    (j : Fin n) (x : Space n) :
    (halfQuadraticRawTest d B).derivative j x = quadraticDatumRawDerivative d B j x := by
  change (∑ a : Fin n, ∑ b : Fin n,
    ((0 : ℝ) * (gradient d.potential x a * gradient d.potential x b) +
      (B a b / 2) * (coordinateHessian d.potential x j a * gradient d.potential x b +
        gradient d.potential x a * coordinateHessian d.potential x j b))) + 0 = _
  simp only [zero_mul, zero_add, add_zero, quadraticDatumRawDerivative]

theorem quadraticSourceDatum_hasLocalWeakDerivative (d : SourceData μ)
    (B : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    HasLocalWeakCoordinateDerivative (quadraticSourceDatum d B : Space n → ℝ)
      (quadraticDatumRawDerivative d B j) j := by
  have hv : (halfQuadraticRawTest d B).value =ᵐ[(volume : Measure (Space n))]
      (quadraticSourceDatum d B : Space n → ℝ) := by
    have he := (volume_absolutelyContinuous_potentialMeasure d.source_C1.continuous).ae_eq
      (quadraticSourceDatum_ae d B)
    filter_upwards [he] with x hx
    rw [halfQuadraticRawTest_value, hx]
  exact ((halfQuadraticRawTest d B).weak_derivative j).congr_ae hv
    (Eventually.of_forall (halfQuadraticRawTest_derivative d B j))

theorem quadraticDatumRawDerivative_memLp (d : SourceData μ)
    (B : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    MemLp (quadraticDatumRawDerivative d B j) 2 (potentialMeasure d.potential) :=
  (memLp_congr_ae (Eventually.of_forall (halfQuadraticRawTest_derivative d B j))).mp
    (ActualBoundedRawSourceCalculus405.BoundedRawTest.ordinary_derivative_memLp
      (halfQuadraticRawTest d B) j)

theorem actual_quadratic_row_differentiated_compact_equation (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (B : Matrix (Fin n) (Fin n) ℝ) (j : Fin n)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) :
    (∑ i : Fin n, ∫ x, quadraticFluxJacobian d hn hμ B i j x * coordinateDerivative ψ i x
      ∂potentialMeasure d.potential) +
      (∑ i : Fin n, ∫ x, coordinateHessian d.potential x i j *
        naturalCanonicalFlux d (quadraticSourceDatum d B) i x * ψ x ∂potentialMeasure d.potential) =
      ∫ x, quadraticDatumRawDerivative d B j x * ψ x ∂potentialMeasure d.potential :=
  natural_flux_differentiated_compact_equation d hn (quadraticSourceDatum d B)
    (quadraticSourceDatum_mean_zero d hμ B) (quadraticFluxJacobian d hn hμ B)
    (fun a _ hE => quadratic_row_flux_local_L2 d hn hμ B a hE)
    (fun a b _ hE => quadratic_flux_jacobian_local_L2 d hn hμ B a b hE)
    (quadratic_flux_jacobian_weak d hn hμ B)
    (quadraticSourceDatum_hasLocalWeakDerivative d B j) hψ hc

end KLSConstantImprovement.ActualQuadraticRowEquation405

#print axioms KLSConstantImprovement.ActualQuadraticRowEquation405.quadraticSourceDatum_hasLocalWeakDerivative
#print axioms KLSConstantImprovement.ActualQuadraticRowEquation405.actual_quadratic_row_differentiated_compact_equation

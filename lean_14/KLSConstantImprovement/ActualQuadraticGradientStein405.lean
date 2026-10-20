import KLSConstantImprovement.ActualGlobalProductStein405
import KLSConstantImprovement.ActualTraceResponse405
import KLSConstantImprovement.ActualCubicGradientEnergy
import KLSConstantImprovement.ActualAffineMatrixTests405

/-! Global second source Stein contraction against a genuine weak
vector gradient. The displayed scalar L2 domains pay every integral;
the final source constructor will instantiate them on its actual Hessian. -/
noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualQuadraticGradientStein405
open KLS ActualBoundedCanonicalSource ActualTraceResponse405
open ActualGlobalProductStein405 ActualCubicGradientEnergy ActualCubicRepresenter
open ActualAffineMatrixTests405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem fullSymmetric_gradient_trace (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j)
    (X : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, ∑ k, T i j k * X k * C i j) =
      ((∑ k, X k • T k) * C).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  have ht : T i j k = T k j i := by rw [hT23 i j k, hT12 i k j, hT23 k i j]
  rw [ht]
  ring

theorem actual_centered_quadratic_gradient_row (d : SourceData μ)
    (B : Matrix (Fin n) (Fin n) ℝ)
    {p : Space n → ℝ} {Dp : Fin n → Space n → ℝ}
    (hp : MemLp p 2 (potentialMeasure d.potential))
    (hDp : ∀ a, MemLp (Dp a) 2 (potentialMeasure d.potential))
    (hw : ∀ a, HasLocalWeakCoordinateDerivative p (Dp a) a) :
    (∫ x, ActualCubicGradientEnergy.centeredQuadratic B (gradient d.potential x) * p x
      ∂potentialMeasure d.potential) =
      (∫ x, (B * (coordinateHessian d.potential x - 1)).trace * p x ∂potentialMeasure d.potential) +
      ∫ x, ∑ j, ∑ k, B j k * gradient d.potential x k * Dp j x ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hX (i : Fin n) : MemLp (fun x => gradient d.potential x i) ∞ (potentialMeasure d.potential) :=
    d.continuous_comp_gradient_memLp (EuclideanSpace.proj i).continuous ∞
  have hx2 (i : Fin n) : MemLp (fun x => gradient d.potential x i) 2 (potentialMeasure d.potential) :=
    (hX i).mono_exponent (by simp)
  have hXX (j k : Fin n) : MemLp (fun x => gradient d.potential x j * gradient d.potential x k)
      2 (potentialMeasure d.potential) := (hX j).mul (hx2 k)
  have hq (j k : Fin n) : Integrable (fun x =>
      B j k * ((gradient d.potential x j * gradient d.potential x k - δ j k) * p x))
      (potentialMeasure d.potential) :=
    (((hXX j k).sub (memLp_const (δ j k))).integrable_mul hp).const_mul _
  have hHp (j k : Fin n) : Integrable (fun x => B j k *
      ((coordinateHessian d.potential x j k - δ j k) * p x)) (potentialMeasure d.potential) :=
    (((d.hessian_entry_memLp j k 2).sub (memLp_const (δ j k))).integrable_mul hp).const_mul _
  have hDpI (j k : Fin n) : Integrable (fun x =>
      B j k * (gradient d.potential x k * Dp j x)) (potentialMeasure d.potential) :=
    ((hx2 k).integrable_mul (hDp j)).const_mul _
  have hrow (j k : Fin n) : (∫ x, B j k *
      ((gradient d.potential x j * gradient d.potential x k - δ j k) * p x)
        ∂potentialMeasure d.potential) =
      (∫ x, B j k * ((coordinateHessian d.potential x j k - δ j k) * p x)
        ∂potentialMeasure d.potential) +
      ∫ x, B j k * (gradient d.potential x k * Dp j x) ∂potentialMeasure d.potential := by
    have hs := actual_global_coordinate_product_stein d hp hDp hw j k
    have hc : Integrable (fun x => δ j k * p x) (potentialMeasure d.potential) :=
      (hp.integrable (by norm_num)).const_mul _
    have hxp : Integrable (fun x => gradient d.potential x j * gradient d.potential x k * p x)
        (potentialMeasure d.potential) := (hXX j k).integrable_mul hp
    have hH : Integrable (fun x => coordinateHessian d.potential x j k * p x)
        (potentialMeasure d.potential) := (d.hessian_entry_memLp j k 2).integrable_mul hp
    simp_rw [sub_mul]
    rw [integral_const_mul, integral_const_mul, integral_const_mul,
      integral_sub hxp hc, integral_sub hH hc]
    rw [hs]
    ring
  have htrace : (fun x => (B * (coordinateHessian d.potential x - 1)).trace * p x)
      =ᵐ[potentialMeasure d.potential] (fun x =>
        ∑ j, ∑ k, B j k * ((coordinateHessian d.potential x j k - δ j k) * p x)) := by
    filter_upwards [d.hessian_ae_source] with x hx
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.sub_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hx.1.isHermitian.isSymm.apply j k]
    have hd : (1 : Matrix (Fin n) (Fin n) ℝ) k j = δ j k := by
      simp [δ, Matrix.one_apply, eq_comm]
    rw [hd]
    ring
  rw [integral_congr_ae htrace]
  simp_rw [centeredQuadratic_eq_sum, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum Finset.univ (fun j _ => integrable_finsetSum Finset.univ fun k _ => hq j k),
    integral_finsetSum Finset.univ (fun j _ => integrable_finsetSum Finset.univ fun k _ => hHp j k),
    integral_finsetSum Finset.univ (fun j _ => integrable_finsetSum Finset.univ fun k _ => hDpI j k)]
  simp_rw [integral_finsetSum Finset.univ (fun k _ => hq _ k),
    integral_finsetSum Finset.univ (fun k _ => hHp _ k),
    integral_finsetSum Finset.univ (fun k _ => hDpI _ k), hrow,
    Finset.sum_add_distrib]

end KLSConstantImprovement.ActualQuadraticGradientStein405
#print axioms KLSConstantImprovement.ActualQuadraticGradientStein405.fullSymmetric_gradient_trace
#print axioms KLSConstantImprovement.ActualQuadraticGradientStein405.actual_centered_quadratic_gradient_row

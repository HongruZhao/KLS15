import KLSConstantImprovement.ActualQuadraticGramProduction405
import KLSConstantImprovement.ActualQuadraticResponseAdjoint405
import KLSConstantImprovement.ActualQuadraticCyclicAdjoint405

/-! Exact literal quadratic-row forcing and its H-weighted trace.
Full symmetry identifies the affine row, while only the actual AE
symmetry of H is used for matrix transposes. -/
noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators
namespace KLSConstantImprovement.ActualQuadraticForcingTrace405
open KLS ActualBoundedCanonicalSource ActualQuadraticGramProduction405 ActualQuadraticRowEquation405
open ActualQuadraticResponseAdjoint405 ActualQuadraticResponseField405 ActualAffineMatrixTests405
open ActualQuadraticHilbertMatrix405 ActualQuadraticCyclicAdjoint405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

def actualQuadraticForcingMatrix (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => actualQuadraticRawForcing d T i j x

def actualQuadraticForcingTrace (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  (coordinateHessian d.potential x * actualQuadraticForcingMatrix d T x).trace

theorem quadraticDatumRawDerivative_eq_affine (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    (i a : Fin n) (x : Space n) :
    quadraticDatumRawDerivative d (T i) a x =
      (coordinateHessian d.potential x *ᵥ actualAffineMatrix d T x i) a := by
  have hz (b : Fin n) : actualAffineMatrix d T x i b = (T i *ᵥ (fun k => (_root_.gradient (F := Space n) d.potential x).ofLp k)) b :=
    full_tensor_affine_row T h12 h23 (fun k => (_root_.gradient (F := Space n) d.potential x).ofLp k) i b
  have hs : (∑ b, ∑ c, (T i b c / 2) * ((_root_.gradient (F := Space n) d.potential x).ofLp b * coordinateHessian d.potential x a c)) =
      ∑ b, ∑ c, (T i b c / 2) * (coordinateHessian d.potential x a b * (_root_.gradient (F := Space n) d.potential x).ofLp c) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by rw [h23 i c b]; ring
  simp only [quadraticDatumRawDerivative, mul_add, Finset.sum_add_distrib]
  rw [hs]
  simp only [Matrix.mulVec, dotProduct, hz, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem actualQuadraticForcingMatrix_eq_ae (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j) :
    actualQuadraticForcingMatrix d T =ᵐ[potentialMeasure d.potential]
      fun x => actualAffineMatrix d T x * coordinateHessian d.potential x * (actualQuadraticFluxMatrix d T x).transpose +
        actualQuadraticFluxMatrix d T x * coordinateHessian d.potential x * (actualAffineMatrix d T x).transpose := by
  filter_upwards [d.hessian_ae_source] with x hx
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i a => quadraticDatumRawDerivative d (T i) a x
  have hD : D = actualAffineMatrix d T x * coordinateHessian d.potential x := by
    ext i a
    change quadraticDatumRawDerivative d (T i) a x = _
    rw [quadraticDatumRawDerivative_eq_affine d T h12 h23]
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun b _ => by rw [hx.1.isHermitian.isSymm.apply a b]; ring
  have hQ : actualQuadraticForcingMatrix d T x =
      D * (actualQuadraticFluxMatrix d T x).transpose + actualQuadraticFluxMatrix d T x * D.transpose := by
    ext i j
    simp only [actualQuadraticForcingMatrix, actualQuadraticRawForcing, Matrix.of_apply,
      Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, actualQuadraticFluxMatrix, D, Finset.sum_add_distrib]
  rw [hQ, hD]
  simp only [Matrix.transpose_mul, hx.1.isHermitian.isSymm.eq, Matrix.mul_assoc]

theorem actual_quadratic_forcing_trace_ae (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j) :
    actualQuadraticForcingTrace d T =ᵐ[potentialMeasure d.potential]
      fun x => 2 * actualQuadraticAffineCrossCost d T x := by
  filter_upwards [d.hessian_ae_source, actualQuadraticForcingMatrix_eq_ae d T h12 h23] with x hx hQ
  let H := coordinateHessian d.potential x
  let U := actualQuadraticFluxMatrix d T x
  let Z := actualAffineMatrix d T x
  have he : (H * Z * H * U.transpose).trace = (H * U * H * Z.transpose).trace := by
    calc
      _ = (H * Z * H * U.transpose).transpose.trace := (Matrix.trace_transpose _).symm
      _ = (U * H * Z.transpose * H).trace := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hx.1.isHermitian.isSymm.eq, H, Matrix.mul_assoc]
      _ = _ := by simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (U * H * Z.transpose) H
  change (H * actualQuadraticForcingMatrix d T x).trace = 2 * (H * U * H * Z.transpose).trace
  rw [hQ, Matrix.mul_add, Matrix.trace_add]
  simp only [← Matrix.mul_assoc]
  rw [he]
  ring

end KLSConstantImprovement.ActualQuadraticForcingTrace405

#print axioms KLSConstantImprovement.ActualQuadraticForcingTrace405.quadraticDatumRawDerivative_eq_affine
#print axioms KLSConstantImprovement.ActualQuadraticForcingTrace405.actual_quadratic_forcing_trace_ae

import QuadraticObservationBridge
import KLS.QuadraticEnergy
import KLS.ActualGradientIntegrability
import KLS.WeakSubgradientTransport

/-! An actual quadratic Appell primitive and its exact adjoint pairing with
the already formalized normalized tilt coefficient. All statements are
unconditional or retain only genuine law/regularity hypotheses. -/

open MeasureTheory ProbabilityTheory InnerProductSpace Matrix Set
open scoped ContDiff BigOperators RealInnerProductSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS.DeterministicBridge

variable {n : ℕ}

/-- The normalized centered quadratic polynomial, i.e. P₂[T]/2!. -/
def quadraticAppellPrimitive (μ : Measure (Space n))
    (T : Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  (1 / 2 : ℝ) * (matrixQuadratic T x - ∫ y, matrixQuadratic T y ∂μ)

theorem isotropic_integral_matrixQuadratic
    {μ : Measure (Space n)} (hiso : IsIsotropic μ)
    (T : Matrix (Fin n) (Fin n) ℝ) :
    (∫ x, matrixQuadratic T x ∂μ) = Matrix.trace T := by
  have he : matrixQuadratic T = fun x : Space n => ∑ i, ∑ j, T i j * (x i * x j) := by
    funext x
    simp only [matrixQuadratic]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
    (fun j _ => (hiso.2.2.1 i j).const_mul (T i j)))]
  simp_rw [integral_finsetSum Finset.univ
    (fun j _ => (hiso.2.2.1 _ j).const_mul (T _ j)), integral_const_mul,
    hiso.integral_coordinate_mul]
  simp [Matrix.trace]

/-- For the released isotropic law, this is exactly (xᵀTx−tr T)/2. -/
theorem quadraticAppellPrimitive_eq_trace
    {μ : Measure (Space n)} (hiso : IsIsotropic μ)
    (T : Matrix (Fin n) (Fin n) ℝ) (x : Space n) :
    quadraticAppellPrimitive μ T x = (matrixQuadratic T x - Matrix.trace T) / 2 := by
  rw [quadraticAppellPrimitive, isotropic_integral_matrixQuadratic hiso]
  ring

theorem quadraticAppellPrimitive_memLp
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hcoord : ∀ i j : Fin n, MemLp (fun x => x i * x j) 2 μ)
    (T : Matrix (Fin n) (Fin n) ℝ) : MemLp (quadraticAppellPrimitive μ T) 2 μ :=
  ((memLp_matrixQuadratic_of_coordinateProducts hcoord T).sub (memLp_const _)).const_mul _

/-- Actual mean zero, rather than a formal polynomial coefficient identity. -/
theorem quadraticAppellPrimitive_integral_eq_zero
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hcoord : ∀ i j : Fin n, MemLp (fun x => x i * x j) 2 μ)
    (T : Matrix (Fin n) (Fin n) ℝ) :
    (∫ x, quadraticAppellPrimitive μ T x ∂μ) = 0 := by
  have hq := memLp_matrixQuadratic_of_coordinateProducts hcoord T
  change (∫ x, (1 / 2 : ℝ) *
    (matrixQuadratic T x - ∫ y, matrixQuadratic T y ∂μ) ∂μ) = 0
  rw [integral_const_mul,
    integral_sub (hq.integrable (by norm_num)) (integrable_const _)]
  simp

/-- This is a genuine centered primitive of the linear tensor field Tx. -/
theorem quadraticAppellPrimitive_gradient
    (μ : Measure (Space n)) (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.IsSymm)
    (x : Space n) : gradient (quadraticAppellPrimitive μ T) x = matrixAction T x := by
  have hdiff : DifferentiableAt ℝ
      (fun y : Space n => matrixQuadratic T y - ∫ z, matrixQuadratic T z ∂μ) x :=
    ((contDiff_matrixQuadratic T).differentiable (by simp) x).sub_const _
  change gradient ((1 / 2 : ℝ) •
    (fun y : Space n => matrixQuadratic T y - ∫ z, matrixQuadratic T z ∂μ)) x = _
  rw [gradient_smul_real hdiff, gradient_sub_const, gradient_matrixQuadratic T hT x,
    smul_smul]
  norm_num

/-- The variance-eight theorem gives exactly two after the factorial 2!. -/
theorem quadraticAppellPrimitive_integral_sq_le_two
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.IsSymm) :
    (∫ x, quadraticAppellPrimitive μ T x ^ 2 ∂μ) ≤ 2 * matrixFrobeniusSq T := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hQ := hμ.quadraticVarianceEight_unconditional
  obtain ⟨hq, hbound⟩ := hQ T hT
  have hp := quadraticAppellPrimitive_memLp hQ.memLp_coordinate_mul T
  have hv : ProbabilityTheory.variance (quadraticAppellPrimitive μ T) μ =
      (1 / 4 : ℝ) * ProbabilityTheory.variance (matrixQuadratic T) μ := by
    change ProbabilityTheory.variance
      (fun x => (1 / 2 : ℝ) * (matrixQuadratic T x - ∫ y, matrixQuadratic T y ∂μ)) μ = _
    rw [ProbabilityTheory.variance_const_mul,
      ProbabilityTheory.variance_sub_const hq.aestronglyMeasurable]
    norm_num
  have he := ProbabilityTheory.variance_eq_sub hp
  rw [quadraticAppellPrimitive_integral_eq_zero hQ.memLp_coordinate_mul T] at he
  change ProbabilityTheory.variance (quadraticAppellPrimitive μ T) μ =
    (∫ x, quadraticAppellPrimitive μ T x ^ 2 ∂μ) - 0 ^ 2 at he
  nlinarith [hbound]

/-- The primitive is exactly the L² adjoint of the quadratic Taylor map,
under the full ordered-coordinate Frobenius pairing. -/
theorem quadraticAppellPrimitive_pairing
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (hcoord : ∀ i j : Fin n, MemLp (fun x => x i * x j) 2 μ)
    (T : Matrix (Fin n) (Fin n) ℝ) :
    (∫ x, f x * quadraticAppellPrimitive μ T x ∂μ) =
      (∑ i, ∑ j, T i j * quadraticCovarianceMatrix μ f i j) / 2 := by
  have hq := memLp_matrixQuadratic_of_coordinateProducts hcoord T
  have he : (fun x => f x * quadraticAppellPrimitive μ T x) =
      fun x => (1 / 2 : ℝ) * (f x * matrixQuadratic T x) -
        ((1 / 2 : ℝ) * ∫ y, matrixQuadratic T y ∂μ) * f x := by
    funext x
    simp only [quadraticAppellPrimitive]
    ring
  have hfm : Integrable (fun x => f x * matrixQuadratic T x) μ :=
    hf.integrable_mul hq
  have h1 : Integrable (fun x => (1 / 2 : ℝ) * (f x * matrixQuadratic T x)) μ :=
    hfm.const_mul (1 / 2 : ℝ)
  have h2 : Integrable
      (fun x => ((1 / 2 : ℝ) * ∫ y, matrixQuadratic T y ∂μ) * f x) μ :=
    (hf.integrable (by norm_num)).const_mul _
  rw [he, integral_sub h1 h2, integral_const_mul, integral_const_mul,
    ← covariance_matrixQuadratic_eq_pairing hf hcoord T,
    covariance_eq_sub hf hq]
  simp only [Pi.mul_apply]
  ring

/-- Exact identification with the literal degree-two normalized tilt Taylor
coefficient already checked in the release. -/
theorem quadraticAppellPrimitive_pairing_eq_Taylor
    {V : Space n → ℝ} {κ : ℝ} [IsProbabilityMeasure (potentialMeasure V)]
    (hV : ContDiff ℝ 2 V) (hκ : 0 < κ) (hstrong : StrongConvexOn univ κ V)
    (hiso : IsIsotropic (potentialMeasure V))
    (f : Lp ℝ 2 (potentialMeasure V)) (T : Matrix (Fin n) (Fin n) ℝ) :
    (∫ x, f x * quadraticAppellPrimitive (potentialMeasure V) T x ∂potentialMeasure V) =
      ∑ i, ∑ j, T i j * exponentialTiltCoordinateTaylor V f 2 ![i, j] := by
  have hLC := measureLogConcave_potentialMeasure hV.continuous.measurable
    (convexOn_of_strongConvexOn_nonneg hκ.le hstrong)
  rw [quadraticAppellPrimitive_pairing (Lp.memLp f) hLC.memLp_two_coordinate_mul T]
  simp_rw [exponentialTiltCoordinateTaylor_two_eq_covariance hV hκ hstrong hiso f]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp_rw [← mul_div_assoc, ← Finset.sum_div]

end KLS.DeterministicBridge
end

#print axioms KLS.DeterministicBridge.quadraticAppellPrimitive_gradient
#print axioms KLS.DeterministicBridge.quadraticAppellPrimitive_integral_sq_le_two
#print axioms KLS.DeterministicBridge.quadraticAppellPrimitive_pairing_eq_Taylor

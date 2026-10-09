import ActualPolynomialAppellProjection
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Bounded operators for actual full-class Appell tensors. Boundedness is
derived from the constructed finite-dimensional polynomial projection.
Their adjoints are genuine L² polynomial representatives, not proposed
coefficient sequences. No universal coefficient bound is assumed. -/
noncomputable section
open MeasureTheory InnerProductSpace Set
open scoped ContDiff ENNReal BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def actualPolynomialSubspace (hμ : admissibleMeasure μ) (d : ℕ) :
    Submodule ℝ (Lp ℝ 2 μ) :=
  LinearMap.range (polynomialCoefficientLpLinearMap hμ.logConcave (degreeExponent n d))

instance actualPolynomialSubspace_finiteDimensional (hμ : admissibleMeasure μ) (d : ℕ) :
    FiniteDimensional ℝ (actualPolynomialSubspace hμ d) :=
  LinearMap.finiteDimensional_range _

instance actualPolynomialSubspace_complete (hμ : admissibleMeasure μ) (d : ℕ) :
    CompleteSpace (actualPolynomialSubspace hμ d) := inferInstance

theorem actualPolynomialSubspace_mem_polynomialLp (hμ : admissibleMeasure μ) (d : ℕ)
    (q : MvPolynomial (Fin n) ℝ) (hq : q.totalDegree ≤ d) :
    polynomialLp hμ.logConcave q ∈ actualPolynomialSubspace hμ d := by
  refine ⟨fun s : DegreeIndex n d => q.coeff s.val,?_⟩
  rw [polynomialCoefficientLp_eq]
  exact congrArg (polynomialLp hμ.logConcave) (boundedDegreePolynomial_representation q hq)

theorem actualPolynomialSubspace_projection_pairings (hμ : admissibleMeasure μ) (d : ℕ)
    (f : Lp ℝ 2 μ) (q : MvPolynomial (Fin n) ℝ) (hq : q.totalDegree ≤ d) :
    (∫ x, polynomialEval q x*((actualPolynomialSubspace hμ d).starProjection f) x ∂μ) =
      ∫ x, polynomialEval q x*f x ∂μ := by
  have ho := (actualPolynomialSubspace hμ d).starProjection_inner_eq_zero f
    (polynomialLp hμ.logConcave q) (actualPolynomialSubspace_mem_polynomialLp hμ d q hq)
  rw [inner_sub_left] at ho
  have he : inner ℝ (polynomialLp hμ.logConcave q)
      ((actualPolynomialSubspace hμ d).starProjection f)=
      inner ℝ (polynomialLp hμ.logConcave q) f := by
    calc
      _ = inner ℝ ((actualPolynomialSubspace hμ d).starProjection f)
          (polynomialLp hμ.logConcave q) := real_inner_comm _ _
      _ = inner ℝ f (polynomialLp hμ.logConcave q) := (sub_eq_zero.mp ho).symm
      _ = _ := real_inner_comm _ _
  simpa only [inner_polynomialLp_eq_integral] using he

theorem actualAppellTensor_projection (hμ : admissibleMeasure μ) (d : ℕ) (f : Lp ℝ 2 μ) :
    fullClassAppellTensor d ((actualPolynomialSubspace hμ d).starProjection f)=
      fullClassAppellTensor d f := by
  apply PiLp.ext
  intro a
  exact actualAppellCoefficient_eq_of_polynomial_pairings hμ.logConcave (Lp.memLp _)
    (Lp.memLp _) (actualPolynomialSubspace_projection_pairings hμ d f) le_rfl a

def actualAppellRestrictedOperator (hμ : admissibleMeasure μ) (d : ℕ) :
    actualPolynomialSubspace hμ d →L[ℝ] EuclideanSpace ℝ (Fin d → Fin n) :=
  ⟨(fullClassAppellLinearMap hμ.logConcave d).domRestrict (actualPolynomialSubspace hμ d),
    LinearMap.continuous_of_finiteDimensional _⟩

/-- The genuine d-th normalized-Laplace derivative as a bounded L² operator. -/
def actualAppellObservation (hμ : admissibleMeasure μ) (d : ℕ) :
    Lp ℝ 2 μ →L[ℝ] EuclideanSpace ℝ (Fin d → Fin n) :=
  (actualAppellRestrictedOperator hμ d).comp
    (actualPolynomialSubspace hμ d).orthogonalProjectionOnto

@[simp] theorem actualAppellObservation_apply (hμ : admissibleMeasure μ) (d : ℕ)
    (f : Lp ℝ 2 μ) : actualAppellObservation hμ d f=fullClassAppellTensor d f :=
  actualAppellTensor_projection hμ d f

theorem actualAppellObservation_norm_sq (hμ : admissibleMeasure μ) (d : ℕ)
    (f : Lp ℝ 2 μ) :
    ‖actualAppellObservation hμ d f‖^2=actualAppellEnergy μ f d := by
  rw [actualAppellObservation_apply,EuclideanSpace.real_norm_sq_eq]
  rfl

/-- The adjoint Appell polynomial is derived from the actual coefficient map. -/
def actualAppellPolynomialLp (hμ : admissibleMeasure μ) (d : ℕ)
    (T : EuclideanSpace ℝ (Fin d → Fin n)) : Lp ℝ 2 μ :=
  (actualAppellObservation hμ d).adjoint T

theorem actualAppellPolynomialLp_mem (hμ : admissibleMeasure μ) (d : ℕ)
    (T : EuclideanSpace ℝ (Fin d → Fin n)) :
    actualAppellPolynomialLp hμ d T ∈ actualPolynomialSubspace hμ d := by
  unfold actualAppellPolynomialLp actualAppellObservation
  rw [ContinuousLinearMap.adjoint_comp,Submodule.adjoint_orthogonalProjectionOnto]
  exact ((actualAppellRestrictedOperator hμ d).adjoint T).property

theorem actualAppellPolynomialLp_pairing (hμ : admissibleMeasure μ) (d : ℕ)
    (T : EuclideanSpace ℝ (Fin d → Fin n)) (f : Lp ℝ 2 μ) :
    inner ℝ (actualAppellPolynomialLp hμ d T) f =
      inner ℝ T (fullClassAppellTensor d f) := by
  exact (ContinuousLinearMap.adjoint_inner_left _ _ _).trans
    (congrArg (inner ℝ T) (actualAppellObservation_apply hμ d f))

theorem actualAppellObservation_opNorm_le_iff (hμ : admissibleMeasure μ) (d : ℕ)
    {C : ℝ} (hC : 0 ≤ C) :
    ‖actualAppellObservation hμ d‖ ≤ Real.sqrt C ↔
      ∀ f : Lp ℝ 2 μ, actualAppellEnergy μ f d ≤ C*‖f‖^2 := by
  constructor
  · intro hb f
    rw [←actualAppellObservation_norm_sq hμ d f]
    have he := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg f))).mpr
      ((actualAppellObservation hμ d).le_of_opNorm_le hb f)
    simpa only [mul_pow,Real.sq_sqrt hC] using he
  · intro hb
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg C)
    intro f
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg f))).mp
    simpa only [mul_pow,Real.sq_sqrt hC,actualAppellObservation_norm_sq] using hb f

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actualAppellObservation
#print axioms KLS.DeterministicBridgeNext.actualAppellObservation_apply
#print axioms KLS.DeterministicBridgeNext.actualAppellPolynomialLp_mem
#print axioms KLS.DeterministicBridgeNext.actualAppellPolynomialLp_pairing
#print axioms KLS.DeterministicBridgeNext.actualAppellObservation_opNorm_le_iff

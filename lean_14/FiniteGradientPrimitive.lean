import ConstantGradientPrimitive
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Finite tensor extension of the genuine vector-forced gradient primitive.
Unlike the old scalar-forced Poisson gradient, this operator lowers the
derivative index. Its inverse identity is proved on the actual gradient range.
No higher symmetric Hodge comparison is asserted in this module. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix
open scoped ContDiff RealInnerProductSpace BigOperators
namespace KLS.DeterministicBridgeIntegration

variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ),
    κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

abbrev VectorField := CenteredL2.Family (potentialMeasure φ) (Fin n)
abbrev TensorField (ι : Type*) [Fintype ι] := PiLp 2 (fun _ : ι => VectorField (φ := φ))
abbrev TensorPrimitive (ι : Type*) [Fintype ι] := PiLp 2 (fun _ : ι => WeightedCenteredH1 φ)

def finiteGradientPrimitive (ι : Type*) [Fintype ι] :
    TensorField (φ := φ) ι →L[ℝ] TensorPrimitive (φ := φ) ι :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => WeightedCenteredH1 φ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i =>
      (weightedGradientPrimitive hφ hκ hlower).comp
        (PiLp.proj 2 (fun _ : ι => VectorField (φ := φ)) i)))

@[simp] theorem finiteGradientPrimitive_apply {ι : Type*} [Fintype ι]
    (F : TensorField (φ := φ) ι) (i : ι) :
    finiteGradientPrimitive hφ hκ hlower ι F i =
      weightedGradientPrimitive hφ hκ hlower (F i) := rfl

def finitePrimitiveValue (ι : Type*) [Fintype ι] :
    TensorPrimitive (φ := φ) ι →L[ℝ] CenteredL2.Family (potentialMeasure φ) ι :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => Lp ℝ 2 (potentialMeasure φ))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i =>
      (weightedH1Value φ).comp
        (PiLp.proj 2 (fun _ : ι => WeightedCenteredH1 φ) i)))

@[simp] theorem finitePrimitiveValue_apply {ι : Type*} [Fintype ι]
    (U : TensorPrimitive (φ := φ) ι) (i : ι) :
    finitePrimitiveValue ι U i = weightedH1Value φ (U i) := rfl

def finitePrimitiveGradient (ι : Type*) [Fintype ι] :
    TensorPrimitive (φ := φ) ι →L[ℝ] TensorField (φ := φ) ι :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => VectorField (φ := φ))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i =>
      (weightedH1Gradient φ).comp
        (PiLp.proj 2 (fun _ : ι => WeightedCenteredH1 φ) i)))

@[simp] theorem finitePrimitiveGradient_apply {ι : Type*} [Fintype ι]
    (U : TensorPrimitive (φ := φ) ι) (i : ι) :
    finitePrimitiveGradient ι U i = weightedH1Gradient φ (U i) := rfl

theorem finiteGradientPrimitive_gradient {ι : Type*} [Fintype ι]
    (U : TensorPrimitive (φ := φ) ι) :
    finiteGradientPrimitive hφ hκ hlower ι (finitePrimitiveGradient ι U) = U := by
  apply PiLp.ext
  intro i
  exact weightedGradientPrimitive_gradient hφ hκ hlower (U i)

theorem finiteGradientPrimitive_reconstruct {ι : Type*} [Fintype ι]
    (F : TensorField (φ := φ) ι)
    (hF : ∀ i, F i ∈ LinearMap.range (weightedH1Gradient φ).toLinearMap) :
    finitePrimitiveGradient ι (finiteGradientPrimitive hφ hκ hlower ι F) = F := by
  apply PiLp.ext
  intro i
  obtain ⟨U, hU⟩ := hF i
  simp only [finitePrimitiveGradient_apply, finiteGradientPrimitive_apply, ← hU]
  change weightedH1Gradient φ
    (weightedGradientPrimitive hφ hκ hlower (weightedH1Gradient φ U)) =
      weightedH1Gradient φ U
  rw [weightedGradientPrimitive_gradient]

theorem finiteGradientPrimitive_integral_eq_zero {ι : Type*} [Fintype ι]
    (F : TensorField (φ := φ) ι) (i : ι) :
    (∫ x, finitePrimitiveValue ι (finiteGradientPrimitive hφ hκ hlower ι F) i x
      ∂potentialMeasure φ) = 0 :=
  weightedGradientPrimitive_integral_eq_zero hφ hκ hlower (F i)

theorem finiteGradientPrimitive_value_norm_le {ι : Type*} [Fintype ι]
    (F : TensorField (φ := φ) ι) :
    ‖finitePrimitiveValue ι (finiteGradientPrimitive hφ hκ hlower ι F)‖ ≤
      Real.sqrt κ⁻¹ * ‖F‖ := by
  have hs : (∑ i, ‖weightedH1Value φ (weightedGradientPrimitive hφ hκ hlower (F i))‖ ^ 2) ≤
      ∑ i, (Real.sqrt κ⁻¹ * ‖F i‖) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    exact (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr
        (weightedGradientPrimitive_value_norm_le hφ hκ hlower (F i))
  have he : (∑ i, (Real.sqrt κ⁻¹ * ‖F i‖) ^ 2) = (Real.sqrt κ⁻¹ * ‖F‖) ^ 2 := by
    simp only [mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  rw [he] at hs
  have hval : ‖finitePrimitiveValue ι (finiteGradientPrimitive hφ hκ hlower ι F)‖ ^ 2 =
      ∑ i, ‖weightedH1Value φ (weightedGradientPrimitive hφ hκ hlower (F i))‖ ^ 2 := by
    simp only [PiLp.norm_sq_eq_of_L2, finitePrimitiveValue_apply, finiteGradientPrimitive_apply]
  rw [← hval] at hs
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hs

theorem finiteGradientPrimitive_constant_norm_sq {ι : Type*} [Fintype ι]
    (hiso : IsIsotropic (potentialMeasure φ)) (T : ι → Space n) :
    ‖finitePrimitiveValue ι (finiteGradientPrimitive hφ hκ hlower ι
      (WithLp.toLp 2 (fun i => constantGradientField (φ := φ) (T i))))‖ ^ 2 =
      ∑ i, ‖T i‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i _
  change ‖weightedH1Value φ (weightedGradientPrimitive hφ hκ hlower
    (constantGradientField (φ := φ) (T i)))‖ ^ 2 = ‖T i‖ ^ 2
  exact weightedGradientPrimitive_constant_norm_sq hφ hκ hlower hiso (T i)

#print axioms finiteGradientPrimitive_gradient
#print axioms finiteGradientPrimitive_reconstruct
#print axioms finiteGradientPrimitive_value_norm_le
#print axioms finiteGradientPrimitive_constant_norm_sq
end KLS.DeterministicBridgeIntegration

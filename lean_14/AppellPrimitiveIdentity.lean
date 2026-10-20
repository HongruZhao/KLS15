import ContractedAppellPolynomials
import ActualGradedTensorOperators
import KLS.WeightedFaithfulGraph

/-! The actual centered inverse gradient integrates contracted genuine
Appell polynomials. Both the graph domain and the normalization are derived. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {φ : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure φ)]

def normalizedContractedAppell (hμ : admissibleMeasure (potentialMeasure φ))
    (d : ℕ) (t : (Fin (d+1) → Fin n) → ℝ) (x : Space n) : ℝ :=
  ((d+1 : ℕ) : ℝ)⁻¹ * polynomialEval (contractedAppellPolynomial hμ (d+1) t) x

theorem normalizedContractedAppell_contDiff (hμ : admissibleMeasure (potentialMeasure φ))
    (d : ℕ) (t : (Fin (d+1) → Fin n) → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (normalizedContractedAppell hμ d t) :=
  contDiff_const.mul (polynomialEval_contDiff _)

theorem normalizedContractedAppell_derivative {κ : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (v : Fin n → ℝ),
      κ*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ y *ᵥ v))
    (hμ : admissibleMeasure (potentialMeasure φ)) (d : ℕ)
    (t : (Fin (d+1) → Fin n) → ℝ)
    (hs : ∀ a b, List.Perm (List.ofFn a) (List.ofFn b) → t a=t b)
    (j : Fin n) (x : Space n) :
    coordinateDerivative (normalizedContractedAppell hμ d t) j x =
      polynomialEval (contractedAppellPolynomial hμ d (fun b => t (Fin.cons j b))) x := by
  have hf : HasFDerivAt (polynomialEval (contractedAppellPolynomial hμ (d+1) t))
      (fderiv ℝ (polynomialEval (contractedAppellPolynomial hμ (d+1) t)) x) x :=
    ((polynomialEval_contDiff _).differentiable (by simp) x).hasFDerivAt
  change fderiv ℝ (fun y => ((d+1 : ℕ) : ℝ)⁻¹ *
    polynomialEval (contractedAppellPolynomial hμ (d+1) t) y) x (EuclideanSpace.single j 1)=_
  have he := congrArg (fun L : Space n →L[ℝ] ℝ => L (EuclideanSpace.single j 1))
    (hf.const_mul ((d+1 : ℕ) : ℝ)⁻¹).fderiv
  simp only [_root_.smul_apply,smul_eq_mul] at he
  rw [he]
  change ((d+1 : ℕ) : ℝ)⁻¹ *
    coordinateDerivative (polynomialEval (contractedAppellPolynomial hμ (d+1) t)) j x=_
  rw [contractedAppellPolynomial_spatial_derivative hφ hκ hlower hμ d t hs]
  have hne : ((d+1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [←mul_assoc,inv_mul_cancel₀ hne,one_mul]

theorem normalizedContractedAppell_integral_zero
    (hμ : admissibleMeasure (potentialMeasure φ)) (d : ℕ)
    (t : (Fin (d+1) → Fin n) → ℝ) :
    (∫ x, normalizedContractedAppell hμ d t x ∂potentialMeasure φ)=0 := by
  change (∫ x, ((d+1 : ℕ) : ℝ)⁻¹ *
    polynomialEval (contractedAppellPolynomial hμ (d+1) t) x ∂potentialMeasure φ)=0
  rw [integral_const_mul,
    contractedAppellPolynomial_integral_zero hμ (by omega : d+1 ≠ 0),mul_zero]

theorem exists_weightedH1_normalizedContractedAppell {κ : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (v : Fin n → ℝ),
      κ*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ y *ᵥ v))
    (hμ : admissibleMeasure (potentialMeasure φ)) (d : ℕ)
    (t : (Fin (d+1) → Fin n) → ℝ)
    (hs : ∀ a b, List.Perm (List.ofFn a) (List.ofFn b) → t a=t b) :
    ∃ U : WeightedCenteredH1 φ,
      (weightedH1Value φ U : Space n → ℝ) =ᵐ[potentialMeasure φ]
        normalizedContractedAppell hμ d t ∧
      ∀ j, (weightedH1Derivative φ j U : Space n → ℝ) =ᵐ[potentialMeasure φ]
        polynomialEval (contractedAppellPolynomial hμ d (fun b => t (Fin.cons j b))) := by
  have hf : MemLp (normalizedContractedAppell hμ d t) 2 (potentialMeasure φ) :=
    (polynomialEval_memLp_two hμ.logConcave _).const_mul _
  have hd (j : Fin n) : MemLp (coordinateDerivative (normalizedContractedAppell hμ d t) j)
      2 (potentialMeasure φ) := by
    have he : coordinateDerivative (normalizedContractedAppell hμ d t) j =
        polynomialEval (contractedAppellPolynomial hμ d (fun b => t (Fin.cons j b))) :=
      funext (normalizedContractedAppell_derivative hφ hκ hlower hμ d t hs j)
    rw [he]
    exact polynomialEval_memLp_two hμ.logConcave _
  obtain ⟨U,hv,hD⟩ := exists_weightedH1_of_faithful_test hφ.continuous
    ⟨((normalizedContractedAppell_contDiff hμ d t).of_le (by simp)).locallyLipschitz,hf⟩
    (energy_lt_top_of_memLp_coordinateDerivative hd)
  refine ⟨U,?_,fun j => ?_⟩
  · simpa only [normalizedContractedAppell_integral_zero,sub_zero] using hv
  · filter_upwards [hD j] with x hx
    exact hx.trans (normalizedContractedAppell_derivative hφ hκ hlower hμ d t hs j x)

theorem weightedGradientPrimitive_normalizedContractedAppell_value {κ : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (v : Fin n → ℝ),
      κ*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ y *ᵥ v))
    (hμ : admissibleMeasure (potentialMeasure φ)) (d : ℕ)
    (t : (Fin (d+1) → Fin n) → ℝ)
    (hs : ∀ a b, List.Perm (List.ofFn a) (List.ofFn b) → t a=t b)
    (G : VectorField (φ := φ))
    (hG : ∀ j, (G j : Space n → ℝ) =ᵐ[potentialMeasure φ]
      polynomialEval (contractedAppellPolynomial hμ d (fun b => t (Fin.cons j b)))) :
    (weightedH1Value φ (weightedGradientPrimitive hφ hκ hlower G) : Space n → ℝ)
      =ᵐ[potentialMeasure φ] normalizedContractedAppell hμ d t := by
  obtain ⟨U,hv,hD⟩ := exists_weightedH1_normalizedContractedAppell hφ hκ hlower hμ d t hs
  have he : weightedH1Gradient φ U=G := by
    apply PiLp.ext
    intro j
    exact Lp.ext ((hD j).trans (hG j).symm)
  rw [←he,weightedGradientPrimitive_gradient]
  exact hv

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.normalizedContractedAppell_derivative
#print axioms KLS.DeterministicBridgeNext.exists_weightedH1_normalizedContractedAppell
#print axioms KLS.DeterministicBridgeNext.weightedGradientPrimitive_normalizedContractedAppell_value

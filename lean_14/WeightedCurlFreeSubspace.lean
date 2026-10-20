import WeightedGradientRangeInverse

/-! The genuine rank-one compatibility condition, expressed by ordinary
distributional curl against smooth compact tests. Its weighted L2 carrier
is a closed submodule. Actual graph gradients belong to it. The converse,
that every such field has a global weighted primitive, is not asserted. -/

open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff RealInnerProductSpace BigOperators

noncomputable section
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ} {φ : Space n → ℝ}

def weightedCurlTestLp (hφ : ContDiff ℝ 1 φ)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (j : Fin n) :
    Lp ℝ 2 (potentialMeasure φ) :=
  (memLp_of_continuous_hasCompactSupport hφ.continuous
    ((contDiff_coordinateDerivative hψ (m := 0) (by simp) j).continuous.mul
      hφ.exp.continuous)
    ((hasCompactSupport_coordinateDerivative hc j).mul_right)).toLp
      (fun x => coordinateDerivative ψ j x * Real.exp (φ x))

theorem weightedCurlTestLp_ae (hφ : ContDiff ℝ 1 φ)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (j : Fin n) :
    (weightedCurlTestLp hφ hψ hc j : Space n → ℝ) =ᵐ[potentialMeasure φ]
      fun x => coordinateDerivative ψ j x * Real.exp (φ x) :=
  (memLp_of_continuous_hasCompactSupport hφ.continuous
    ((contDiff_coordinateDerivative hψ (m := 0) (by simp) j).continuous.mul
      hφ.exp.continuous)
    ((hasCompactSupport_coordinateDerivative hc j).mul_right)).coeFn_toLp

/-- Weighted L2 pairing with the density-cancelled compact test represents
the actual unweighted distributional pairing. -/
theorem weightedCurlTestLp_inner (hφ : ContDiff ℝ 1 φ)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (j : Fin n)
    (f : Lp ℝ 2 (potentialMeasure φ)) :
    inner ℝ (weightedCurlTestLp hφ hψ hc j) f =
      ∫ x, f x * coordinateDerivative ψ j x := by
  rw [L2.inner_def]
  have he : (∫ x, inner ℝ (weightedCurlTestLp hφ hψ hc j x) (f x)
      ∂potentialMeasure φ) =
      ∫ x, (f x * coordinateDerivative ψ j x) * Real.exp (φ x)
        ∂potentialMeasure φ := by
    apply integral_congr_ae
    filter_upwards [weightedCurlTestLp_ae hφ hψ hc j] with x hx
    simp only [hx, RCLike.inner_apply, conj_trivial]
    ring
  rw [he, integral_potentialMeasure hφ.continuous.measurable]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    calc
      _ = (f x * coordinateDerivative ψ j x) *
        (Real.exp (φ x) * Real.exp (-φ x)) := by ring
      _ = _ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

def weightedCurlTestFunctional (hφ : ContDiff ℝ 1 φ)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (i j : Fin n) :
    CenteredL2.Family (potentialMeasure φ) (Fin n) →L[ℝ] ℝ :=
  (innerSL ℝ (weightedCurlTestLp hφ hψ hc j)).comp
      (PiLp.proj 2 (fun _ : Fin n => Lp ℝ 2 (potentialMeasure φ)) i) -
    (innerSL ℝ (weightedCurlTestLp hφ hψ hc i)).comp
      (PiLp.proj 2 (fun _ : Fin n => Lp ℝ 2 (potentialMeasure φ)) j)

theorem weightedCurlTestFunctional_apply (hφ : ContDiff ℝ 1 φ)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (i j : Fin n)
    (F : CenteredL2.Family (potentialMeasure φ) (Fin n)) :
    weightedCurlTestFunctional hφ hψ hc i j F =
      (∫ x, F i x * coordinateDerivative ψ j x) -
        ∫ x, F j x * coordinateDerivative ψ i x := by
  simp only [weightedCurlTestFunctional, _root_.sub_apply,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply, innerSL_apply_apply,
    weightedCurlTestLp_inner]

/-- The rank-one compatibility space uses genuine ordinary distributional
curl, represented by bounded weighted L2 test functionals. -/
def weightedCurlFreeSubspace (hφ : ContDiff ℝ 1 φ) :
    Submodule ℝ (CenteredL2.Family (potentialMeasure φ) (Fin n)) :=
  ⨅ (ψ : Space n → ℝ), ⨅ (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ), ⨅ (hc : HasCompactSupport ψ),
    ⨅ (i : Fin n), ⨅ (j : Fin n),
      LinearMap.ker (weightedCurlTestFunctional hφ hψ hc i j).toLinearMap

theorem mem_weightedCurlFreeSubspace_iff (hφ : ContDiff ℝ 1 φ)
    (F : CenteredL2.Family (potentialMeasure φ) (Fin n)) :
    F ∈ weightedCurlFreeSubspace hφ ↔
      ∀ (ψ : Space n → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        ∀ i j : Fin n,
          (∫ x, F i x * coordinateDerivative ψ j x) =
            ∫ x, F j x * coordinateDerivative ψ i x := by
  simp only [weightedCurlFreeSubspace, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h ψ hψ hc i j
    have he := h ψ hψ hc i j
    change weightedCurlTestFunctional hφ hψ hc i j F = 0 at he
    rw [weightedCurlTestFunctional_apply] at he
    exact sub_eq_zero.mp he
  · intro h ψ hψ hc i j
    change weightedCurlTestFunctional hφ hψ hc i j F = 0
    rw [weightedCurlTestFunctional_apply]
    exact sub_eq_zero.mpr (h ψ hψ hc i j)

theorem weightedCurlFreeSubspace_isClosed (hφ : ContDiff ℝ 1 φ) :
    IsClosed (weightedCurlFreeSubspace hφ :
      Set (CenteredL2.Family (potentialMeasure φ) (Fin n))) := by
  simp only [weightedCurlFreeSubspace, Submodule.coe_iInf]
  exact isClosed_iInter fun ψ => isClosed_iInter fun hψ => isClosed_iInter fun hc =>
    isClosed_iInter fun i => isClosed_iInter fun j =>
      (weightedCurlTestFunctional hφ hψ hc i j).isClosed_ker

theorem weightedGradientRange_le_curlFreeSubspace (hφ : ContDiff ℝ 1 φ) :
    LinearMap.range (weightedH1Gradient φ).toLinearMap ≤ weightedCurlFreeSubspace hφ := by
  rintro F ⟨U, rfl⟩
  rw [mem_weightedCurlFreeSubspace_iff]
  intro ψ hψ hc i j
  exact weightedH1Gradient_distributionally_curlFree hφ U i j hψ hc

theorem weightedGradientProjection_mem_curlFreeSubspace
    {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (F : CenteredL2.Family (potentialMeasure φ) (Fin n)) :
    weightedGradientProjection hφ hκ hlower F ∈
      weightedCurlFreeSubspace (hφ.of_le (by norm_num)) :=
  weightedGradientRange_le_curlFreeSubspace (hφ.of_le (by norm_num))
    ⟨weightedGradientPrimitive hφ hκ hlower F, rfl⟩

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.weightedCurlTestLp_inner
#print axioms KLS.DeterministicBridgeIntegration.mem_weightedCurlFreeSubspace_iff
#print axioms KLS.DeterministicBridgeIntegration.weightedCurlFreeSubspace_isClosed
#print axioms KLS.DeterministicBridgeIntegration.weightedGradientRange_le_curlFreeSubspace
#print axioms KLS.DeterministicBridgeIntegration.weightedGradientProjection_mem_curlFreeSubspace

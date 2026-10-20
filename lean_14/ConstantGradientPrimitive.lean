import WeightedGradientRangeInverse
import KLS.WeightedFaithfulGraph
import KLS.ThirdCumulant

/-! The constructed inverse actually integrates constant vector fields to
linear polynomials for isotropic laws. This verifies a concrete action of
the genuine range inverse, not merely the norm of a proposed polynomial. -/

open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff RealInnerProductSpace BigOperators ENNReal

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ} {φ : Space n → ℝ}

def constantGradientField [IsProbabilityMeasure (potentialMeasure φ)] (a : Space n) :
    CenteredL2.Family (potentialMeasure φ) (Fin n) :=
  WithLp.toLp 2 (fun i => a i • CenteredL2.oneLp (potentialMeasure φ))

theorem constantGradientField_ae [IsProbabilityMeasure (potentialMeasure φ)]
    (a : Space n) (i : Fin n) :
    (constantGradientField (φ := φ) a i : Space n → ℝ) =ᵐ[potentialMeasure φ]
      fun _ => a i := by
  filter_upwards [Lp.coeFn_smul (a i) (CenteredL2.oneLp (potentialMeasure φ)),
    CenteredL2.oneLp_ae (potentialMeasure φ)] with x hx hy
  change (a i • CenteredL2.oneLp (potentialMeasure φ)) x = _
  rw [hx, Pi.smul_apply, smul_eq_mul, hy, mul_one]

theorem gradient_linear_inner (a x : Space n) :
    gradient (fun y => inner ℝ a y) x = a := by
  have hfun : (fun y : Space n => inner ℝ a y) = ⇑(innerSL ℝ a) := by
    funext y
    exact (innerSL_apply_apply ℝ a y).symm
  have hd := (innerSL ℝ a).hasFDerivAt (x := x)
  rw [← hfun] at hd
  apply (toDual ℝ (Space n)).injective
  rw [toDual_gradient, hd.fderiv]
  ext y
  simp [toDual_apply_apply]

theorem linear_inner_energy [IsProbabilityMeasure (potentialMeasure φ)]
    (a : Space n) :
    energy (potentialMeasure φ) (fun y => inner ℝ a y) = ENNReal.ofReal (‖a‖ ^ 2) := by
  unfold energy
  simp only [gradient_linear_inner]
  simp

theorem exists_weightedH1_linear_inner [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : Continuous φ) (hiso : IsIsotropic (potentialMeasure φ)) (a : Space n) :
    ∃ U : WeightedCenteredH1 φ,
      (weightedH1Value φ U : Space n → ℝ) =ᵐ[potentialMeasure φ]
        (fun x => inner ℝ a x) ∧
      weightedH1Gradient φ U = constantGradientField a := by
  have hinner : (fun x : Space n => inner ℝ a x) = fun x => inner ℝ x a :=
    funext fun x => real_inner_comm _ _
  have hf : LocallyLipschitzTests (potentialMeasure φ) (fun x => inner ℝ a x) := by
    refine ⟨(innerSL ℝ a).lipschitzWith.locallyLipschitz, ?_⟩
    rw [hinner]
    exact hiso.memLp_inner a
  have he : energy (potentialMeasure φ) (fun x => inner ℝ a x) < ⊤ := by
    rw [linear_inner_energy]
    exact ENNReal.ofReal_lt_top
  obtain ⟨U, hv, hd⟩ := exists_weightedH1_of_faithful_test hφ hf he
  have hm : (∫ x, inner ℝ a x ∂potentialMeasure φ) = 0 := by
    rw [hinner]
    exact hiso.integral_inner a
  refine ⟨U, ?_, ?_⟩
  · simpa only [hm, sub_zero] using hv
  · apply PiLp.ext
    intro i
    apply Lp.ext
    filter_upwards [hd i, constantGradientField_ae (φ := φ) a i] with x hx hy
    change weightedH1Derivative φ i U x = _
    rw [hx, hy, coordinateDerivative_eq_gradient, gradient_linear_inner]

/-- The newly constructed operator, not just an abstract primitive, sends
the actual constant vector field a to the actual centered linear test. -/
theorem weightedGradientPrimitive_constant_value_ae
    {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (b : Fin n → ℝ),
      κ * (b ⬝ᵥ b) ≤ b ⬝ᵥ (coordinateHessian φ x *ᵥ b))
    (hiso : IsIsotropic (potentialMeasure φ)) (a : Space n) :
    (weightedH1Value φ
      (weightedGradientPrimitive hφ hκ hlower (constantGradientField a)) : Space n → ℝ)
        =ᵐ[potentialMeasure φ] fun x => inner ℝ a x := by
  obtain ⟨U, hv, hG⟩ := exists_weightedH1_linear_inner hφ.continuous hiso a
  rw [← hG, weightedGradientPrimitive_gradient]
  exact hv

theorem weightedGradientPrimitive_constant_norm_sq
    {κ : ℝ} [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (b : Fin n → ℝ),
      κ * (b ⬝ᵥ b) ≤ b ⬝ᵥ (coordinateHessian φ x *ᵥ b))
    (hiso : IsIsotropic (potentialMeasure φ)) (a : Space n) :
    ‖weightedH1Value φ
      (weightedGradientPrimitive hφ hκ hlower (constantGradientField a))‖ ^ 2 =
        ‖a‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  calc
    _ = ∫ x, (inner ℝ x a) ^ 2 ∂potentialMeasure φ := by
      apply integral_congr_ae
      filter_upwards [weightedGradientPrimitive_constant_value_ae hφ hκ hlower hiso a]
        with x hx
      simp only [hx, RCLike.inner_apply, conj_trivial]
      rw [show inner ℝ a x = inner ℝ x a from real_inner_comm _ _]
      ring
    _ = ‖a‖ ^ 2 := hiso.integral_inner_sq a

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.exists_weightedH1_linear_inner
#print axioms KLS.DeterministicBridgeIntegration.weightedGradientPrimitive_constant_value_ae
#print axioms KLS.DeterministicBridgeIntegration.weightedGradientPrimitive_constant_norm_sq

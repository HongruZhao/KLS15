import ActualIndividualObservationCaps

/-! Retain the joint two-head observation Gram instead of maximizing the
heads independently. This is a globally valid inequality for actual bounded
Hilbert operators, and its separate-norm fallback recovers the old bound.
No improved universal numerical norm for this Gram is asserted. -/
noncomputable section
open InnerProductSpace ContinuousLinearMap
open scoped ContDiff
namespace KLSImprovement.ObservationGram
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {H E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def retainedHeadGram (O₁ O₂ : H →L[ℝ] E) (a b : ℝ) : H →L[ℝ] H :=
  a • (O₁.adjoint.comp O₁) + b • (O₂.adjoint.comp O₂)

theorem retainedHeadGram_quadratic (O₁ O₂ : H →L[ℝ] E) (a b : ℝ) (f : H) :
    inner ℝ (retainedHeadGram O₁ O₂ a b f) f = a*‖O₁ f‖^2+b*‖O₂ f‖^2 := by
  have h₁ := apply_norm_sq_eq_inner_adjoint_left O₁ f
  have h₂ := apply_norm_sq_eq_inner_adjoint_left O₂ f
  simp only [RCLike.re_to_real] at h₁ h₂
  simp only [retainedHeadGram, add_apply, smul_apply, inner_add_left,
    real_inner_smul_left]
  rw [← h₁, ← h₂]

theorem retained_head_bound (O₁ O₂ : H →L[ℝ] E) (a b : ℝ) (f : H) :
    a*‖O₁ f‖^2+b*‖O₂ f‖^2 ≤ ‖retainedHeadGram O₁ O₂ a b‖*‖f‖^2 := by
  rw [← retainedHeadGram_quadratic]
  calc
    _ ≤ ‖retainedHeadGram O₁ O₂ a b f‖*‖f‖ := real_inner_le_norm _ _
    _ ≤ (‖retainedHeadGram O₁ O₂ a b‖*‖f‖)*‖f‖ :=
      mul_le_mul_of_nonneg_right ((retainedHeadGram O₁ O₂ a b).le_opNorm f) (norm_nonneg _)
    _ = _ := by ring

theorem retained_head_norm_le_separate (O₁ O₂ : H →L[ℝ] E)
    {a b : ℝ} (ha : 0≤a) (hb : 0≤b) :
    ‖retainedHeadGram O₁ O₂ a b‖ ≤ a*‖O₁‖^2+b*‖O₂‖^2 := by
  calc
    _ ≤ ‖a • (O₁.adjoint.comp O₁)‖+‖b • (O₂.adjoint.comp O₂)‖ := norm_add_le _ _
    _ = _ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha, abs_of_nonneg hb]
      simp only [ContinuousLinearMap.norm_adjoint_comp_self, pow_two]

/-- A prefix bound retaining the actual joint two-head quadratic form.
The head coefficients may encode the rate factors and denominator weights. -/
theorem prefix_bound_with_retained_heads
    (O₁ O₂ : H →L[ℝ] E) (f : H) {a b P C v : ℝ}
    (hP : P≤C) (hv : 0<v) :
    a*‖O₁ f‖^2+b*‖O₂ f‖^2+P/v ≤
      ‖retainedHeadGram O₁ O₂ a b‖*‖f‖^2+C/v := by
  exact add_le_add (retained_head_bound O₁ O₂ a b f)
    (div_le_div_of_nonneg_right hP hv.le)

end KLSImprovement.ObservationGram

namespace KLSImprovement.ObservationGram
open MeasureTheory Matrix KLS KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- Literal actual graded observation used by the existing two-head endgame. -/
def actualHeadObservation
    {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hiso : IsIsotropic (potentialMeasure φ)) (d : ℕ) :
    GradedCenteredTensorHilbert hφ →L[ℝ] GradedConstantTensorHilbert hφ :=
  (gradedConstantIntegration hφ hκ hlower hiso).adjoint.comp
    ((gradedTensorIntegration hφ hκ hlower).adjoint^d)

def actualRetainedHeadGram
    {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hiso : IsIsotropic (potentialMeasure φ)) (a b : ℝ) :
    GradedCenteredTensorHilbert hφ →L[ℝ] GradedCenteredTensorHilbert hφ :=
  retainedHeadGram (actualHeadObservation hφ hκ hlower hiso 1)
    (actualHeadObservation hφ hκ hlower hiso 2) a b

theorem actual_retained_head_bound
    {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hiso : IsIsotropic (potentialMeasure φ)) (a b : ℝ)
    (f : GradedCenteredTensorHilbert hφ) :
    a*‖actualHeadObservation hφ hκ hlower hiso 1 f‖^2+
      b*‖actualHeadObservation hφ hκ hlower hiso 2 f‖^2 ≤
      ‖actualRetainedHeadGram hφ hκ hlower hiso a b‖*‖f‖^2 :=
  retained_head_bound (actualHeadObservation hφ hκ hlower hiso 1)
    (actualHeadObservation hφ hκ hlower hiso 2) a b f

end KLSImprovement.ObservationGram

#print axioms KLSImprovement.ObservationGram.retainedHeadGram_quadratic
#print axioms KLSImprovement.ObservationGram.retained_head_bound
#print axioms KLSImprovement.ObservationGram.retained_head_norm_le_separate
#print axioms KLSImprovement.ObservationGram.prefix_bound_with_retained_heads
#print axioms KLSImprovement.ObservationGram.actual_retained_head_bound

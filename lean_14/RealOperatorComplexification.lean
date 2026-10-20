import RealHilbertComplexification
import CanonicalResolvent

/-! Norm-preserving complexification of actual real bounded operators.
This closes the scalar-field change; it does not construct the weighted
tensor operators or assume their comparison and Appell estimates. -/
noncomputable section
namespace KLSBelow25
namespace RealHilbertComplexification
open ContinuousLinearMap InnerProductSpace
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {H F G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

@[simp] theorem extend_zero : extend (0 : H →L[ℝ] F)=0 := by
  ext x <;> rfl

@[simp] theorem extend_add (S T : H →L[ℝ] F) : extend (S+T)=extend S+extend T := by
  ext x <;> rfl

@[simp] theorem extend_sub (S T : H →L[ℝ] F) : extend (S-T)=extend S-extend T := by
  ext x <;> rfl

@[simp] theorem extend_smul (a : ℝ) (T : H →L[ℝ] F) : extend (a • T)=a • extend T := by
  ext x <;> simp [← Complex.coe_smul]

@[simp] theorem extend_one : extend (1 : H →L[ℝ] H)=1 := by
  ext x <;> rfl

@[simp] theorem extend_comp (S : F →L[ℝ] G) (T : H →L[ℝ] F) :
    extend (S.comp T)=(extend S).comp (extend T) := by
  ext x <;> rfl

@[simp] theorem extend_mul (S T : H →L[ℝ] H) : extend (S*T)=extend S*extend T :=
  extend_comp S T

@[simp] theorem extend_pow (T : H →L[ℝ] H) (j : ℕ) : extend (T^j)=extend T^j := by
  induction j with
  | zero => simp
  | succ j hj => simp [pow_succ,hj]

variable [CompleteSpace H] [CompleteSpace F]

@[simp] theorem extend_adjoint (T : H →L[ℝ] F) : extend T.adjoint=(extend T).adjoint := by
  apply (eq_adjoint_iff _ _).mpr
  intro x y
  apply Complex.ext <;>
    simp only [inner_re,inner_im,extend_re,extend_im,adjoint_inner_left]

def realIntegrationGram (R : H →L[ℝ] H) (L : F →L[ℝ] H) : H →L[ℝ] H :=
  R.comp R.adjoint+L.comp L.adjoint

theorem realIntegrationGram_isPositive (R : H →L[ℝ] H) (L : F →L[ℝ] H) :
    (realIntegrationGram R L).IsPositive :=
  (isPositive_self_comp_adjoint R).add (isPositive_self_comp_adjoint L)

@[simp] theorem extend_realIntegrationGram (R : H →L[ℝ] H) (L : F →L[ℝ] H) :
    extend (realIntegrationGram R L)=integrationGram (extend R) (extend L) := by
  simp [realIntegrationGram,integrationGram]

def realCanonicalIntegrationResolvent (R : H →L[ℝ] H) (L : F →L[ℝ] H) (a : ℝ) : H →L[ℝ] H :=
  Ring.inverse (1+a • realIntegrationGram R L)

theorem realCanonicalIntegrationResolvent_inverse
    (R : H →L[ℝ] H) (L : F →L[ℝ] H) {a : ℝ} (ha : 0 ≤ a) :
    (1+a • realIntegrationGram R L)*realCanonicalIntegrationResolvent R L a=1 :=
  Ring.mul_inverse_cancel _ (positive_resolvent_isUnit _ (realIntegrationGram_isPositive R L) ha)

theorem extend_realCanonicalIntegrationResolvent
    (R : H →L[ℝ] H) (L : F →L[ℝ] H) {a : ℝ} (ha : 0 ≤ a) :
    extend (realCanonicalIntegrationResolvent R L a)=
      canonicalIntegrationResolvent (extend R) (extend L) a := by
  have he := congrArg extend (realCanonicalIntegrationResolvent_inverse R L ha)
  simp only [extend_mul,extend_add,extend_one,extend_smul,extend_realIntegrationGram] at he
  have hu := complex_positive_resolvent_isUnit
    (integrationGram (extend R) (extend L)) (integrationGram_isPositive _ _) ha
  exact (IsUnit.mul_left_cancel hu) (he.trans
    (canonicalIntegrationResolvent_inverse (extend R) (extend L) ha).symm)

def realRationalIntegrationComparison (R : H →L[ℝ] H) (L : F →L[ℝ] H) (a : ℝ) : Prop :=
  ∀ v : H, ‖R v‖^2 ≤ ⟪(a⁻¹ • (1-realCanonicalIntegrationResolvent R L a)) v,v⟫_ℝ

theorem rationalIntegrationComparison_extend
    (R : H →L[ℝ] H) (L : F →L[ℝ] H) {a : ℝ} (ha : 0 ≤ a)
    (h : realRationalIntegrationComparison R L a) :
    rationalIntegrationComparison (extend R) (extend L) a := by
  intro v
  have he := extend_realCanonicalIntegrationResolvent R L ha
  rw [← he]
  have hmap : a⁻¹ • (1-extend (realCanonicalIntegrationResolvent R L a))=
      extend (a⁻¹ • (1-realCanonicalIntegrationResolvent R L a)) := by simp
  rw [hmap, norm_sq,inner_re,extend_re,extend_im]
  exact add_le_add (h v.re) (h v.im)

theorem real_canonical_operator_endpoint_twentyFive
    (R : H →L[ℝ] H) (L : F →L[ℝ] H) {a : ℝ} (ha : 0 < a)
    (hcomparison : realRationalIntegrationComparison R L a)
    (hobs1 : ‖R.comp L‖^2 ≤ 2)
    (hobs : ∀ j : ℕ, ‖(R^(j+2)).comp L‖^2 ≤ (121/4 : ℝ)*(223/10 : ℝ)^j) :
    1+‖R‖^2 ≤ 25 := by
  have h := canonical_operator_endpoint_twentyFive (extend R) (extend L) ha
    (rationalIntegrationComparison_extend R L ha.le hcomparison)
    (by simpa only [← extend_comp,norm_extend] using hobs1)
    (fun j => by simpa only [← extend_pow,← extend_comp,norm_extend] using hobs j)
  simpa only [norm_extend] using h

theorem real_canonical_operator_endpoint_twentyFour886
    (R : H →L[ℝ] H) (L : F →L[ℝ] H) {a : ℝ} (ha : 0 < a)
    (hcomparison : realRationalIntegrationComparison R L a)
    (hobs1 : ‖R.comp L‖^2 ≤ 2)
    (hobs : ∀ j : ℕ, ‖(R^(j+2)).comp L‖^2 ≤ (121/4 : ℝ)*(2221/100 : ℝ)^j) :
    1+‖R‖^2 ≤ (12443/500 : ℝ) := by
  have h := canonical_operator_endpoint_twentyFour886 (extend R) (extend L) ha
    (rationalIntegrationComparison_extend R L ha.le hcomparison)
    (by simpa only [← extend_comp,norm_extend] using hobs1)
    (fun j => by simpa only [← extend_pow,← extend_comp,norm_extend] using hobs j)
  simpa only [norm_extend] using h

#print axioms extend_adjoint
#print axioms extend_realCanonicalIntegrationResolvent
#print axioms rationalIntegrationComparison_extend
#print axioms real_canonical_operator_endpoint_twentyFive
#print axioms real_canonical_operator_endpoint_twentyFour886
end RealHilbertComplexification
end KLSBelow25

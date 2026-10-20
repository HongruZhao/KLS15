import CompatibleTensorOperators
import GradedResolventComparison

/-! The paper's actual graded operators on its closed compatible tensor
spaces. The bounds used for their construction are the already proved
measure-dependent strong-convexity bound. The dimension-free curvature
comparison and Appell observation bounds remain explicitly separate. -/
noncomputable section
open MeasureTheory Matrix InnerProductSpace
open scoped ContDiff ENNReal
namespace KLS.DeterministicBridgeIntegration
open KLSBelow25 KLSBelow25.GradedHilbert KLSBelow25.RealHilbertComplexification
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ),
    κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

abbrev GradedCenteredTensorHilbert :=
  lp (CenteredCompatibleTensorHilbert (hφ.of_le (by simp))) 2
abbrev GradedConstantTensorHilbert :=
  lp (fun r => ConstantCompatibleTensorHilbert (hφ.of_le (by simp)) (r+1)) 2

theorem centeredTensorIntegration_opNorm_le (r : ℕ) :
    ‖centeredTensorIntegration hφ hκ hlower r‖ ≤ Real.sqrt κ⁻¹ := by
  exact ContinuousLinearMap.opNorm_le_bound (centeredTensorIntegration hφ hκ hlower r)
    (Real.sqrt_nonneg _) (fun F => compatibleTensorPrimitive_norm_le hφ hκ hlower
      (r := r) (F : OrderedTensorField φ (r+1)))

def gradedTensorIntegration : GradedCenteredTensorHilbert hφ →L[ℝ] GradedCenteredTensorHilbert hφ :=
  shift (centeredTensorIntegration hφ hκ hlower) (Real.sqrt_nonneg _)
    (centeredTensorIntegration_opNorm_le hφ hκ hlower)

def gradedConstantIntegration (hiso : IsIsotropic (potentialMeasure φ)) :
    GradedConstantTensorHilbert hφ →L[ℝ] GradedCenteredTensorHilbert hφ :=
  diagonal (constantTensorIntegration hφ hκ hlower) zero_le_one
    (constantTensorIntegration_opNorm_le_one hφ hκ hlower hiso)

@[simp] theorem gradedTensorIntegration_apply (F : GradedCenteredTensorHilbert hφ) (r : ℕ) :
    gradedTensorIntegration hφ hκ hlower F r=centeredTensorIntegration hφ hκ hlower r (F (r+1)) := rfl

@[simp] theorem gradedConstantIntegration_apply (hiso : IsIsotropic (potentialMeasure φ))
    (F : GradedConstantTensorHilbert hφ) (r : ℕ) :
    gradedConstantIntegration hφ hκ hlower hiso F r=constantTensorIntegration hφ hκ hlower r (F r) := rfl

theorem gradedTensorIntegration_norm_le :
    ‖gradedTensorIntegration hφ hκ hlower‖ ≤ Real.sqrt κ⁻¹ :=
  norm_shift_le _ _ _

theorem gradedConstantIntegration_norm_le_one (hiso : IsIsotropic (potentialMeasure φ)) :
    ‖gradedConstantIntegration hφ hκ hlower hiso‖ ≤ 1 := norm_diagonal_le _ _ _

theorem centeredTensorIntegration_norm_le_graded (r : ℕ) :
    ‖centeredTensorIntegration hφ hκ hlower r‖ ≤ ‖gradedTensorIntegration hφ hκ hlower‖ :=
  norm_block_le_shift _ _ _ r

/-- This predicate is precisely the still-required geometric block estimate;
it is not asserted here. Its operands are the actual weighted primitives. -/
def ActualTensorCurvatureComparison : Prop :=
  ∀ r (v : CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) (r+1)),
    ‖centeredTensorIntegration hφ hκ hlower r v‖^2 ≤
      ⟪(κ⁻¹ • (1-blockResolvent (centeredTensorIntegration hφ hκ hlower)
        (constantTensorIntegration hφ hκ hlower) κ (r+1))) v,v⟫_ℝ

theorem actual_graded_rational_comparison (hiso : IsIsotropic (potentialMeasure φ))
    (hcomparison : ActualTensorCurvatureComparison hφ hκ hlower) :
    realRationalIntegrationComparison (gradedTensorIntegration hφ hκ hlower)
      (gradedConstantIntegration hφ hκ hlower hiso) κ :=
  gradedRationalIntegrationComparison _ _ _ _ _ _ hκ.le hcomparison

/-- Conditional bridge on actual weighted operators. It is not a universal
Poincare theorem: the geometric and Appell hypotheses are still displayed. -/
theorem actual_graded_norm_twentyFive_of_analytic_bounds
    (hiso : IsIsotropic (potentialMeasure φ))
    (hcomparison : ActualTensorCurvatureComparison hφ hκ hlower)
    (hobs1 : ‖(gradedTensorIntegration hφ hκ hlower).comp
      (gradedConstantIntegration hφ hκ hlower hiso)‖^2 ≤ 2)
    (hobs : ∀ j : ℕ, ‖((gradedTensorIntegration hφ hκ hlower)^(j+2)).comp
      (gradedConstantIntegration hφ hκ hlower hiso)‖^2 ≤ (121/4 : ℝ)*(223/10 : ℝ)^j) :
    1+‖gradedTensorIntegration hφ hκ hlower‖^2 ≤ 25 :=
  real_canonical_operator_endpoint_twentyFive _ _ hκ
    (actual_graded_rational_comparison hφ hκ hlower hiso hcomparison) hobs1 hobs

theorem actual_graded_norm_twentyFour886_of_analytic_bounds
    (hiso : IsIsotropic (potentialMeasure φ))
    (hcomparison : ActualTensorCurvatureComparison hφ hκ hlower)
    (hobs1 : ‖(gradedTensorIntegration hφ hκ hlower).comp
      (gradedConstantIntegration hφ hκ hlower hiso)‖^2 ≤ 2)
    (hobs : ∀ j : ℕ, ‖((gradedTensorIntegration hφ hκ hlower)^(j+2)).comp
      (gradedConstantIntegration hφ hκ hlower hiso)‖^2 ≤ (121/4 : ℝ)*(2221/100 : ℝ)^j) :
    1+‖gradedTensorIntegration hφ hκ hlower‖^2 ≤ (12443/500 : ℝ) :=
  real_canonical_operator_endpoint_twentyFour886 _ _ hκ
    (actual_graded_rational_comparison hφ hκ hlower hiso hcomparison) hobs1 hobs

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.gradedTensorIntegration
#print axioms KLS.DeterministicBridgeIntegration.actual_graded_rational_comparison
#print axioms KLS.DeterministicBridgeIntegration.actual_graded_norm_twentyFive_of_analytic_bounds
#print axioms KLS.DeterministicBridgeIntegration.actual_graded_norm_twentyFour886_of_analytic_bounds

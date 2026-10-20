import ActualKLS149963Endpoints
import OperatorThreshold14992816
import ActualAffineSchur

/-!
Replace the rank-zero triangle/Cauchy estimate by the exact affine Schur
criterion on the original closed compatible tensor carriers.  Existing global
analytic estimates imply the joint criterion at the established endpoint, so
the unconditional proof remains complete.  The criterion can subsequently
accept a stronger joint estimate without changing this endpoint bridge.

This module does not assert the missing universal joint estimate at four.
-/

noncomputable section
open MeasureTheory Matrix
open scoped ContDiff ENNReal NNReal
namespace KLSImprovement.ActualSchurEndpoint
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSBelow25.CoupledEnergy KLSBelow25.RealHilbertComplexification
open KLSImprovement.OperatorThreshold14992816
open KLSImprovement.ActualAffineSchur
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- Existing norm information implies the exact joint Schur condition at the
same constant.  Stronger joint information can replace this sufficient bound. -/
theorem actual_joint_schur_of_graded_norm_bound
    {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hiso : IsIsotropic (potentialMeasure φ))
    {C : ℝ} (hC : 1 < C)
    (hgraded : 1 + ‖gradedTensorIntegration hφ hκ hlower‖ ^ 2 ≤ C) :
    ActualRankZeroJointSchurBound hφ hκ hlower C := by
  intro G
  let J := centeredTensorIntegration hφ hκ hlower 0
  let L := constantTensorIntegration hφ hκ hlower 0
  have hJ : ‖J‖ ≤ ‖gradedTensorIntegration hφ hκ hlower‖ :=
    centeredTensorIntegration_norm_le_graded hφ hκ hlower 0
  have hJ2 : ‖J‖ ^ 2 ≤ C - 1 := by
    have hs := (sq_le_sq₀ (norm_nonneg J)
      (norm_nonneg (gradedTensorIntegration hφ hκ hlower))).mpr hJ
    linarith
  have hpoint : ‖J G‖ ^ 2 ≤ (C - 1) * ‖G‖ ^ 2 := by
    have hn := (sq_le_sq₀ (norm_nonneg (J G))
      (mul_nonneg (norm_nonneg J) (norm_nonneg G))).mpr (J.le_opNorm G)
    rw [mul_pow] at hn
    exact hn.trans (mul_le_mul_of_nonneg_right hJ2 (sq_nonneg ‖G‖))
  have hL : ‖L.adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact constantTensorIntegration_opNorm_le_one hφ hκ hlower hiso 0
  have hobsnorm : ‖L.adjoint (J G)‖ ≤ ‖J G‖ := by
    calc
      _ ≤ ‖L.adjoint‖ * ‖J G‖ := L.adjoint.le_opNorm (J G)
      _ ≤ 1 * ‖J G‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
      _ = ‖J G‖ := one_mul _
  have hobs : ‖L.adjoint (J G)‖ ^ 2 ≤ (C - 1) * ‖G‖ ^ 2 :=
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hobsnorm).trans hpoint
  have hpos : 0 < C - 1 := sub_pos.mpr hC
  have hcharge : (C - 1)⁻¹ * ‖L.adjoint (J G)‖ ^ 2 ≤ ‖G‖ ^ 2 := by
    calc
      _ ≤ (C - 1)⁻¹ * ((C - 1) * ‖G‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hobs (inv_nonneg.mpr hpos.le)
      _ = ‖G‖ ^ 2 := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
  change ‖J G‖ ^ 2 + (C - 1)⁻¹ * ‖L.adjoint (J G)‖ ^ 2 ≤ C * ‖G‖ ^ 2
  nlinarith [hpoint, hcharge]

theorem graded_norm_of_unchanged_analytic_bounds
    {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hμ : admissibleMeasure (potentialMeasure φ))
    (hcoupled : ∀ (N : ℕ) (f : Lp ℝ 2 (potentialMeasure φ)),
      actualWeightedAppellEnergy (potentialMeasure φ) f rate N ≤ budget * ‖f‖ ^ 2)
    (hthree : ∀ f : Lp ℝ 2 (potentialMeasure φ),
      actualAppellEnergy (potentialMeasure φ) f 3 ≤ (36 * (49 / 2) : ℝ) * ‖f‖ ^ 2) :
    1 + ‖gradedTensorIntegration hφ hκ hlower‖ ^ 2 ≤ bound := by
  have hraw : ∀ (N : ℕ) (f : Lp ℝ 2 (potentialMeasure φ)),
      ∑ d ∈ Finset.Icc 2 N,
        rate⁻¹ ^ d * actualAppellEnergy (potentialMeasure φ) f d /
          (d.factorial : ℝ) ^ 2 ≤ budget * ‖f‖ ^ 2 := by
    intro N f
    convert hcoupled N f using 1
    unfold actualWeightedAppellEnergy
    apply Finset.sum_congr rfl
    intro d hd
    simp only [_root_.mul_inv_rev, inv_pow, div_eq_mul_inv]
    ring
  have hbudget : jointObservationBudget
      (gradedTensorIntegration hφ hκ hlower)
      (gradedConstantIntegration hφ hκ hlower hμ.isotropic) rate budget := by
    intro N f
    exact actual_joint_graded_observability hφ hκ hlower hμ
      rate_positive budget_positive.le hraw N f
  have hcap1 (f : GradedCenteredTensorHilbert hφ) :
      rate⁻¹ ^ 2 * ‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
        (((gradedTensorIntegration hφ hκ hlower).adjoint ^ 1) f)‖ ^ 2 ≤ firstCap * ‖f‖ ^ 2 := by
    have hb := actual_first_graded_observation_sq_le hφ hκ hlower hμ f
    norm_num [rate, firstCap] at hb ⊢
    nlinarith
  have hcap2 (f : GradedCenteredTensorHilbert hφ) :
      rate⁻¹ ^ 3 * ‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
        (((gradedTensorIntegration hφ hκ hlower).adjoint ^ 2) f)‖ ^ 2 ≤ secondCap * ‖f‖ ^ 2 := by
    have hb := actual_individual_graded_observation_sq_le hφ hκ hlower hμ 2
      (by norm_num : (0 : ℝ) ≤ 36 * (49 / 2)) hthree f
    norm_num [rate, secondCap] at hb ⊢
    nlinarith
  have hb := real_canonical_operator_endpoint_two_head_budget
    (gradedTensorIntegration hφ hκ hlower)
    (gradedConstantIntegration hφ hκ hlower hμ.isotropic)
    hκ rate_positive budget_positive.le threshold_gt_one caps_nonneg.1 caps_nonneg.2
    caps_sum_le_budget secondLower_ge_threshold thirdLower_ge_second
    (by rfl : secondLower ≤ threshold ^ 2 - firstCap)
    (by rfl : thirdLower ≤ secondLower * (threshold - firstCap / threshold) - secondCap)
    residualRatio_gt_one cost_identity.le
    (actual_graded_rational_comparison hφ hκ hlower hμ.isotropic
      (actual_tensor_curvature_comparison hφ hκ hlower)) hbudget hcap1 hcap2
  rw [endpoint_value] at hb
  exact hb

/-- The complete regular endpoint now passes through the exact actual Schur
condition instead of the former primitive triangle estimate. -/
theorem regularPoincare14992816
    {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hn : 0 < n) (hμ : admissibleMeasure (potentialMeasure φ)) :
    poincareConstant (potentialMeasure φ) ≤ ENNReal.ofReal bound := by
  apply poincareConstant_le_of_actual_joint_schur hφ hκ hlower hn hμ.isotropic
    (by norm_num [bound])
  apply actual_joint_schur_of_graded_norm_bound hφ hκ hlower hμ.isotropic
    (by norm_num [bound])
  apply graded_norm_of_unchanged_analytic_bounds hφ hκ hlower hμ
  · intro N f
    exact actual_weighted_appell_energy_thirteen_four_norm_sq_le N hμ f
  · intro f
    simpa only [KLSBelow25.SymmetricCenteredSeed245.B] using
      actual_appell_energy_three_symmetric245_le_norm_sq hμ f

theorem poincare14992816_mem {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    (937051 / 62500 : ℝ≥0) ∈ poincareConstants μ := by
  apply mem_poincareConstants_of_paperRegularDensity hμ (by norm_num)
  intro ν hν hregular
  obtain ⟨V, κ, hV, hκ, hstrong, hupper, hgrowth, heq⟩ := hregular
  subst ν
  let : IsProbabilityMeasure (potentialMeasure V) := hν.isProb
  let hlower := coordinateHessian_lower_of_strongConvexOn (hV.of_le (by simp)) hstrong
  have hc := regularPoincare14992816 hV hκ hlower (by omega) hν
  have hfin : poincareConstant (potentialMeasure V) < ⊤ := hc.trans_lt ENNReal.ofReal_lt_top
  apply (poincareConstants_iff_optimal_le (poincareConstants_nonempty_iff.mpr hfin)
    (hν.poincareConstant_pos hn)).mpr
  convert hc using 1
  unfold bound
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 62500)]
  norm_num

theorem poincare14992816 {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : LocallyLipschitzTests μ f) :
    variance μ f ≤ (937051 / 62500 : ℝ≥0∞) * energy μ f := by
  simpa using poincare14992816_mem hn hμ f hf

theorem universalPoincareUpper14992816 :
    universalPoincareConstant ≤ (937051 / 62500 : ℝ≥0∞) := by
  apply universal_le_iff.mpr
  intro n hn μ hμ
  simpa using poincareConstant_le_of_mem (poincare14992816_mem hn hμ)

theorem openaiPoincare14992816 {n : ℕ} (hn : 1 ≤ n)
    {ρ : OAI.LeanBlast.KLS.Space n → ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (hiso : OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ)
      ((937051 : ℝ) / 62500) :=
  OpenAIBridge.poincareBound_of_mem hρ
    (poincare14992816_mem hn (OpenAIBridge.admissible hρ hiso))

theorem openaiKLS14992816 : OAI.LeanBlast.KLS.KLSStatement := by
  refine ⟨((937051 : ℝ) / 62500), by norm_num, ?_⟩
  intro n hn ρ hρ hiso
  exact openaiPoincare14992816 hn hρ hiso

end KLSImprovement.ActualSchurEndpoint

#print axioms KLSImprovement.ActualSchurEndpoint.actual_joint_schur_of_graded_norm_bound
#print axioms KLSImprovement.ActualSchurEndpoint.graded_norm_of_unchanged_analytic_bounds
#print axioms KLSImprovement.ActualSchurEndpoint.regularPoincare14992816
#print axioms KLSImprovement.ActualSchurEndpoint.poincare14992816_mem
#print axioms KLSImprovement.ActualSchurEndpoint.universalPoincareUpper14992816
#print axioms KLSImprovement.ActualSchurEndpoint.openaiPoincare14992816
#print axioms KLSImprovement.ActualSchurEndpoint.openaiKLS14992816

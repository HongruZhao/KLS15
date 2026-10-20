import KLSConstantImprovement.ParameterizedWeightedBudget
import TwoHeadObservationOperatorEndgame
import ActualIndividualObservationCaps
import ActualRegularEndpointCoupled
import ActualCreationCubicSeed239Cap
import ActualKLS149963Endpoints

/-! Actual regular and original-class endpoint transfer for a certified scalar
weighted profile. All analytic caps, graded realization, curvature comparison,
operator endgame, and regular-density transfer are discharged by existing
actual-law theorems. A new endpoint requires a concrete scalar certificate. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix
open scoped BigOperators ContDiff ENNReal NNReal
namespace KLSConstantImprovement.ParameterizedWeightedEndpoint
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSBelow25.RealHilbertComplexification
open KLSConstantImprovement.ParameterizedWeightedBudget
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

def firstCap (P : Parameters) : ℝ := 2/P.K^2
def secondCap (P : Parameters) : ℝ := CreationSeed239.B/P.K^3

structure TwoHeadParameters where
  p : ℝ
  u : ℝ
  v : ℝ
  r : ℝ

/-- This is a scalar recurrence certificate, not an analytic assumption. -/
structure TwoHeadCertificate (P : Parameters) (O : TwoHeadParameters) : Prop where
  p_gt_one : 1 < O.p
  caps_sum : firstCap P+secondCap P ≤ P.C
  p_le_u : O.p ≤ O.u
  u_le_v : O.u ≤ O.v
  u_initial : O.u ≤ O.p^2-firstCap P
  v_initial : O.v ≤ O.u*(O.p-firstCap P/O.p)-secondCap P
  r_gt_one : 1 < O.r
  total_cost : O.r+firstCap P/O.p+secondCap P/O.u+
    (P.C-firstCap P-secondCap P)/O.v ≤ O.p

variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ),
    κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
  (hμ : admissibleMeasure (potentialMeasure φ))

theorem actual_joint_observation_budget (P : Parameters) (h : ScalarCertificate P) :
    CoupledEnergy.jointObservationBudget (gradedTensorIntegration hφ hκ hlower)
      (gradedConstantIntegration hφ hκ hlower hμ.isotropic) P.K P.C := by
  have hraw : ∀ (N : ℕ) (f : Lp ℝ 2 (potentialMeasure φ)),
      ∑ d ∈ Finset.Icc 2 N, P.K⁻¹^d*actualAppellEnergy (potentialMeasure φ) f d/
        (d.factorial : ℝ)^2 ≤ P.C*‖f‖^2 := by
    intro N f
    have hh := actual_weighted_energy_norm_sq_le P h N hμ f
    convert hh using 1
    unfold actualWeightedAppellEnergy
    apply Finset.sum_congr rfl
    intro d hd
    simp only [_root_.mul_inv_rev,inv_pow,div_eq_mul_inv]
    ring
  intro N f
  exact actual_joint_graded_observability hφ hκ hlower hμ h.K_positive h.C_nonneg hraw N f

theorem actual_first_observation_cap (P : Parameters) (h : ScalarCertificate P)
    (f : GradedCenteredTensorHilbert hφ) :
    P.K⁻¹^2*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
      (((gradedTensorIntegration hφ hκ hlower).adjoint^1) f)‖^2 ≤ firstCap P*‖f‖^2 := by
  have hb := actual_first_graded_observation_sq_le hφ hκ hlower hμ f
  have hm := mul_le_mul_of_nonneg_left hb (pow_nonneg (inv_nonneg.mpr h.K_positive.le) 2)
  convert hm using 1
  simp only [firstCap,inv_pow,div_eq_mul_inv]
  ring

theorem actual_second_observation_cap (P : Parameters) (h : ScalarCertificate P)
    (f : GradedCenteredTensorHilbert hφ) :
    P.K⁻¹^3*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
      (((gradedTensorIntegration hφ hκ hlower).adjoint^2) f)‖^2 ≤ secondCap P*‖f‖^2 := by
  have hB : 0 ≤ 36*CreationSeed239.B := by positivity [CreationSeed239.B_positive]
  have hb := actual_individual_graded_observation_sq_le hφ hκ hlower hμ 2 hB
    (actual_appell_energy_three_creation239_le_norm_sq hμ) f
  have hm := mul_le_mul_of_nonneg_left hb (pow_nonneg (inv_nonneg.mpr h.K_positive.le) 3)
  norm_num only [Nat.reduceAdd,Nat.factorial] at hm
  convert hm using 1
  simp only [secondCap,inv_pow,div_eq_mul_inv]
  ring

include hμ in
theorem actual_graded_operator_endpoint (P : Parameters) (h : ScalarCertificate P)
    (O : TwoHeadParameters) (ho : TwoHeadCertificate P O) :
    1+‖gradedTensorIntegration hφ hκ hlower‖^2 ≤ 1+P.K*O.p := by
  have ha : 0 ≤ firstCap P := div_nonneg (by norm_num) (sq_nonneg _)
  have hb : 0 ≤ secondCap P := div_nonneg CreationSeed239.B_positive.le (pow_nonneg h.K_positive.le _)
  exact real_canonical_operator_endpoint_two_head_budget
    (gradedTensorIntegration hφ hκ hlower)
    (gradedConstantIntegration hφ hκ hlower hμ.isotropic)
    hκ h.K_positive h.C_nonneg ho.p_gt_one ha hb ho.caps_sum ho.p_le_u ho.u_le_v
    ho.u_initial ho.v_initial ho.r_gt_one ho.total_cost
    (actual_graded_rational_comparison hφ hκ hlower hμ.isotropic
      (actual_tensor_curvature_comparison hφ hκ hlower))
    (actual_joint_observation_budget hφ hκ hlower hμ P h)
    (actual_first_observation_cap hφ hκ hlower hμ P h)
    (actual_second_observation_cap hφ hκ hlower hμ P h)

include hφ hκ hlower hμ in
theorem regular_poincare (P : Parameters) (h : ScalarCertificate P)
    (O : TwoHeadParameters) (ho : TwoHeadCertificate P O) (hn : 0 < n) :
    poincareConstant (potentialMeasure φ) ≤ ENNReal.ofReal (1+P.K*O.p) :=
  (poincareConstant_le_one_add_graded_norm_sq hφ hκ hlower hn hμ.isotropic).trans
    (ENNReal.ofReal_le_ofReal (actual_graded_operator_endpoint hφ hκ hlower hμ P h O ho))

end KLSConstantImprovement.ParameterizedWeightedEndpoint

namespace KLSConstantImprovement.ParameterizedWeightedEndpoint
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.ParameterizedWeightedBudget
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

theorem original_poincare_mem (P : Parameters) (h : ScalarCertificate P)
    (O : TwoHeadParameters) (ho : TwoHeadCertificate P O) (target : ℝ≥0)
    (hbound : 1+P.K*O.p ≤ (target : ℝ))
    {n : ℕ} (hn : 1 ≤ n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    target ∈ poincareConstants μ := by
  have hp : 0 < P.K*O.p := mul_pos h.K_positive (by linarith [ho.p_gt_one])
  have ht : (0 : ℝ) < target := by linarith
  apply mem_poincareConstants_of_paperRegularDensity hμ (show 0 < target by exact_mod_cast ht)
  intro ν hν hregular
  obtain ⟨V,κ,hV,hκ,hstrong,hupper,hgrowth,heq⟩ := hregular
  subst ν
  let : IsProbabilityMeasure (potentialMeasure V) := hν.isProb
  let hlower := coordinateHessian_lower_of_strongConvexOn (hV.of_le (by simp)) hstrong
  have hc := regular_poincare hV hκ hlower hν P h O ho (by omega)
  have hb : ENNReal.ofReal (1+P.K*O.p) ≤ (target : ℝ≥0∞) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hbound
  have hfinal := hc.trans hb
  have hfin : poincareConstant (potentialMeasure V) < ⊤ := hfinal.trans_lt (by simp)
  apply (poincareConstants_iff_optimal_le (poincareConstants_nonempty_iff.mpr hfin)
    (hν.poincareConstant_pos hn)).mpr
  exact hfinal

theorem original_poincare (P : Parameters) (h : ScalarCertificate P)
    (O : TwoHeadParameters) (ho : TwoHeadCertificate P O) (target : ℝ≥0)
    (hbound : 1+P.K*O.p ≤ (target : ℝ))
    {n : ℕ} (hn : 1 ≤ n) {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : LocallyLipschitzTests μ f) :
    variance μ f ≤ (target : ℝ≥0∞)*energy μ f :=
  original_poincare_mem P h O ho target hbound hn hμ f hf

theorem universal_poincare_upper (P : Parameters) (h : ScalarCertificate P)
    (O : TwoHeadParameters) (ho : TwoHeadCertificate P O) (target : ℝ≥0)
    (hbound : 1+P.K*O.p ≤ (target : ℝ)) :
    universalPoincareConstant ≤ (target : ℝ≥0∞) := by
  apply universal_le_iff.mpr
  intro n hn μ hμ
  exact poincareConstant_le_of_mem (original_poincare_mem P h O ho target hbound hn hμ)

end KLSConstantImprovement.ParameterizedWeightedEndpoint
#print axioms KLSConstantImprovement.ParameterizedWeightedEndpoint.actual_graded_operator_endpoint
#print axioms KLSConstantImprovement.ParameterizedWeightedEndpoint.original_poincare_mem
#print axioms KLSConstantImprovement.ParameterizedWeightedEndpoint.universal_poincare_upper

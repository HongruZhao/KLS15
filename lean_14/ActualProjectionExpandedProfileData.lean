import ActualSeed239ExpandedAdjointEnvelope
import ProjectionExpandedProfileNumerics
import CorrelatedInitializationOperatorEndgame
import ActualCorrelatedCubicTangentCaps239
import ActualRegularEndpointCoupled
import ActualWeightedAppellInductionSeed239Expanded

/-! Actual law/test data at the proposed finite-anchor parameters.
This exports proved inputs only; no improved operator endpoint is asserted. -/
noncomputable section
open MeasureTheory Matrix Set InnerProductSpace
open scoped ContDiff ENNReal BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration KLSBelow25.RealHilbertComplexification
open KLSBelow25.ProjectionExpandedProfileNumerics
set_option maxHeartbeats 110000000
set_option backward.isDefEq.respectTransparency false

theorem actual_projection_expanded_profile_data
    {n : ℕ} {φ : Space n→ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0<κ)
    (hlower : ∀ x (a : Fin n→ℝ),
      κ*(a ⬝ᵥ a)≤a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hμ : admissibleMeasure (potentialMeasure φ)) :
    let R := gradedTensorIntegration hφ hκ hlower
    let L := gradedConstantIntegration hφ hκ hlower hμ.isotropic
    KLSBelow25.CoupledEnergy.jointObservationBudget R L K C ∧
    (∀ f : GradedCenteredTensorHilbert hφ,
      K⁻¹^2*‖L.adjoint ((R.adjoint^1) f)‖^2≤firstCap*‖f‖^2) ∧
    (∀ f : GradedCenteredTensorHilbert hφ, ‖f‖=1 →
      thirdLower≤(p^2-K⁻¹^2*‖L.adjoint ((R.adjoint^1) f)‖^2)*
        (p-(K⁻¹^2*‖L.adjoint ((R.adjoint^1) f)‖^2)/p)-
        K⁻¹^3*‖L.adjoint ((R.adjoint^2) f)‖^2) ∧
    (∀ f : GradedCenteredTensorHilbert hφ,
      weight1*(K⁻¹^2*‖L.adjoint ((R.adjoint^1) f)‖^2)+
      weight2*(K⁻¹^3*‖L.adjoint ((R.adjoint^2) f)‖^2)≤ supportCap*‖f‖^2) := by
  have hraw : ∀ (N : ℕ) (f : Lp ℝ 2 (potentialMeasure φ)),
      ∑d∈Finset.Icc 2 N,K⁻¹^d*actualAppellEnergy (potentialMeasure φ) f d/(d.factorial : ℝ)^2≤C*‖f‖^2 := by
    intro N f
    have hh : actualWeightedAppellEnergy (potentialMeasure φ) f K N≤C*‖f‖^2 := by
      simpa only [K,C,KLSBelow25.CoupledEnergy.NumericsSeed239Expanded.K,
        KLSBelow25.CoupledEnergy.NumericsSeed239Expanded.C] using
          actual_weighted_appell_energy_seed239_expanded_norm_sq_le N hμ f
    convert hh using 1
    unfold actualWeightedAppellEnergy
    apply Finset.sum_congr rfl
    intro d hd
    simp only [_root_.mul_inv_rev,inv_pow,div_eq_mul_inv]
    ring
  have hbudget : KLSBelow25.CoupledEnergy.jointObservationBudget
      (gradedTensorIntegration hφ hκ hlower)
      (gradedConstantIntegration hφ hκ hlower hμ.isotropic) K C := by
    intro N f
    exact actual_joint_graded_observability hφ hκ hlower hμ K_positive (by norm_num [C] : 0≤C) hraw N f
  have hcap1 (f : GradedCenteredTensorHilbert hφ) :
      K⁻¹^2*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
        (((gradedTensorIntegration hφ hκ hlower).adjoint^1) f)‖^2≤firstCap*‖f‖^2 := by
    have hb := actual_first_graded_observation_sq_le hφ hκ hlower hμ f
    norm_num [K,firstCap] at hb ⊢
    nlinarith
  obtain ⟨ha,hpu,hpv,hu,hw1,hw2,hD⟩ := head_parameters
  have hinit (f : GradedCenteredTensorHilbert hφ) (hf : ‖f‖=1) :
      thirdLower≤(p^2-K⁻¹^2*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
        (((gradedTensorIntegration hφ hκ hlower).adjoint^1) f)‖^2)*
        (p-(K⁻¹^2*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
          (((gradedTensorIntegration hφ hκ hlower).adjoint^1) f)‖^2)/p)-
        K⁻¹^3*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
          (((gradedTensorIntegration hφ hκ hlower).adjoint^2) f)‖^2 := by
    apply correlated_initialization (by positivity)
      (by simpa only [hf,one_pow,mul_one] using hcap1 f)
    have hh := actual_correlated_cubic_graded_cap_creation239 hφ hκ hlower hμ f
    simp only [hf,one_pow,mul_one] at hh
    have harg : (K⁻¹^2*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
        (((gradedTensorIntegration hφ hκ hlower).adjoint^1) f)‖^2)/firstCap =
        ‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
          (((gradedTensorIntegration hφ hκ hlower).adjoint^1) f)‖^2/2 := by
      unfold firstCap
      field_simp [K_positive.ne']
    rw [harg]
    have hm := mul_le_mul_of_nonneg_left hh (pow_nonneg (inv_nonneg.mpr K_positive.le) 3)
    convert hm using 1
    simp only [secondCap,KLSBelow25.CreationSeed239.B,inv_pow,div_eq_mul_inv]
    ring
  have hjoint (f : GradedCenteredTensorHilbert hφ) :
      weight1*(K⁻¹^2*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
        (((gradedTensorIntegration hφ hκ hlower).adjoint^1) f)‖^2)+
      weight2*(K⁻¹^3*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
        (((gradedTensorIntegration hφ hκ hlower).adjoint^2) f)‖^2)≤ supportCap*‖f‖^2 := by
    have hh := actual_correlated_cubic_graded_supporting_cap_creation239 hφ hκ hlower hμ
      (a := weight1/K^2) (b := weight2/K^3)
      (div_nonneg hw1 (sq_nonneg _))
      (div_nonneg hw2 (pow_nonneg K_positive.le _)) hD
      (fun z hz => actual_seed_support hz) f
    convert hh using 1
    simp only [inv_pow,div_eq_mul_inv]
    ring
  exact ⟨hbudget,hcap1,hinit,hjoint⟩

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_projection_expanded_profile_data

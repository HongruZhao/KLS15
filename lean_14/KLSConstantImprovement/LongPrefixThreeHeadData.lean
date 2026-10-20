import KLSConstantImprovement.LongPrefixThreeHeadNumerics
import ActualCorrelatedQuarticObservationCaps200000
import CorrelatedInitializationOperatorEndgame
import ActualCorrelatedCubicTangentCaps239
import ActualRegularEndpointCoupled

/-! Actual law/test data at the proposed finite-anchor parameters.
These three caps use the same original scalar tests before the graded lift.
This exports proved inputs only; no improved operator endpoint is asserted. -/
noncomputable section
open MeasureTheory Matrix Set InnerProductSpace
open scoped ContDiff ENNReal BigOperators
namespace KLSConstantImprovement.LongPrefixThreeHeadData
open KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration KLSBelow25.RealHilbertComplexification
open KLSConstantImprovement.LongPrefixThreeHeadNumerics
set_option maxHeartbeats 110000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 600000

theorem actual_long_prefix_three_head_data
    {n : ℕ} {φ : Space n→ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0<κ)
    (hlower : ∀ x (a : Fin n→ℝ),
      κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hμ : admissibleMeasure (potentialMeasure φ)) :
    let R := gradedTensorIntegration hφ hκ hlower
    let L := gradedConstantIntegration hφ hκ hlower hμ.isotropic
    (∀ f : GradedCenteredTensorHilbert hφ,
      K⁻¹^2*‖L.adjoint ((R.adjoint^1) f)‖^2 ≤ firstCap*‖f‖^2) ∧
    (∀ f : GradedCenteredTensorHilbert hφ, ‖f‖=1 →
      thirdLower ≤ (p^2-K⁻¹^2*‖L.adjoint ((R.adjoint^1) f)‖^2)*
        (p-(K⁻¹^2*‖L.adjoint ((R.adjoint^1) f)‖^2)/p)-
        K⁻¹^3*‖L.adjoint ((R.adjoint^2) f)‖^2) ∧
    (∀ f : GradedCenteredTensorHilbert hφ,
      initialWeight*(K⁻¹^2*‖L.adjoint ((R.adjoint^1) f)‖^2)+
      (2*init4_r)*(K⁻¹^3*‖L.adjoint ((R.adjoint^2) f)‖^2)+
      K⁻¹^4*‖L.adjoint ((R.adjoint^3) f)‖^2 ≤ initialHeight*‖f‖^2) ∧
    (∀ f : GradedCenteredTensorHilbert hφ,
      weight1*(K⁻¹^2*‖L.adjoint ((R.adjoint^1) f)‖^2)+
      weight2*(K⁻¹^3*‖L.adjoint ((R.adjoint^2) f)‖^2)+
      weight3*(K⁻¹^4*‖L.adjoint ((R.adjoint^3) f)‖^2) ≤ supportCap*‖f‖^2) := by
  have hcap1 (f : GradedCenteredTensorHilbert hφ) :
      K⁻¹^2*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
        (((gradedTensorIntegration hφ hκ hlower).adjoint^1) f)‖^2 ≤ firstCap*‖f‖^2 := by
    have hb := actual_first_graded_observation_sq_le hφ hκ hlower hμ f
    norm_num [K,firstCap] at hb ⊢
    nlinarith
  obtain ⟨hp,hu,hv,hw,hr,hrcap,hw1,hw2,hw3,hD4,hD⟩ := numerical_parameters
  have hinit (f : GradedCenteredTensorHilbert hφ) (hf : ‖f‖=1) :
      thirdLower ≤ (p^2-K⁻¹^2*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
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
  have hinit4 (f : GradedCenteredTensorHilbert hφ) :
      initialWeight*(K⁻¹^2*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
        (((gradedTensorIntegration hφ hκ hlower).adjoint^1) f)‖^2)+
      (2*init4_r)*(K⁻¹^3*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
        (((gradedTensorIntegration hφ hκ hlower).adjoint^2) f)‖^2)+
      K⁻¹^4*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
        (((gradedTensorIntegration hφ hκ hlower).adjoint^3) f)‖^2 ≤ initialHeight*‖f‖^2 := by
    have hh := actual_normalized_correlated_quartic_graded_supporting_cap_creation200000
      hφ hκ hlower hμ (a := initialWeight) (b := 2*init4_r) (c := 1) (H := initialHeight)
      K_positive initialWeight_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hr) (by norm_num : (0 : ℝ) ≤ 1) hD4
      (fun u hu v hv hcurve => by simpa only [mul_one] using initial_shape u hu v hv hcurve) f
    simpa only [one_mul] using hh
  have hjoint (f : GradedCenteredTensorHilbert hφ) :
      weight1*(K⁻¹^2*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
        (((gradedTensorIntegration hφ hκ hlower).adjoint^1) f)‖^2)+
      weight2*(K⁻¹^3*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
        (((gradedTensorIntegration hφ hκ hlower).adjoint^2) f)‖^2)+
      weight3*(K⁻¹^4*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
        (((gradedTensorIntegration hφ hκ hlower).adjoint^3) f)‖^2) ≤ supportCap*‖f‖^2 :=
    actual_normalized_correlated_quartic_graded_supporting_cap_creation200000
      hφ hκ hlower hμ K_positive hw1 hw2 hw3 hD head_shape f
  exact ⟨hcap1,hinit,hinit4,hjoint⟩

end KLSConstantImprovement.LongPrefixThreeHeadData
#print axioms KLSConstantImprovement.LongPrefixThreeHeadData.actual_long_prefix_three_head_data

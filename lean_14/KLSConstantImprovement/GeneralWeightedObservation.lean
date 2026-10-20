import KLSConstantImprovement.MicroWeightedAdjointEnvelope
import ProjectionThreeHeadFiniteChargeCost

/-! Arbitrary positive observation weights lift to actual tensor ranks.
A uniform positive weight floor supplies the spectral envelope. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Matrix ContinuousLinearMap
open scoped ContDiff BigOperators RealInnerProductSpace Topology ENNReal
namespace KLSConstantImprovement.GeneralWeightedObservation
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration KLSBelow25
open KLSBelow25.GradedHilbert KLSBelow25.RealHilbertComplexification
open KLSBelow25.CoupledEnergy
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {φ : Space n→ℝ} {κ : ℝ}
variable [IsProbabilityMeasure (potentialMeasure φ)]
variable (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0<κ)
  (hlower : ∀ x (v : Fin n→ℝ), κ*(v ⬝ᵥ v)≤v ⬝ᵥ (coordinateHessian φ x *ᵥ v))
  (hμ : admissibleMeasure (potentialMeasure φ))

theorem actual_general_observation_block_le {C : ℝ} (a : ℕ→ℝ) (ha : ∀ d, 0≤a d)
    (hcoupled : ∀ (N : ℕ) (f : Lp ℝ 2 (potentialMeasure φ)),
      ∑d∈Finset.Icc 2 N,a d*actualAppellEnergy (potentialMeasure φ) f d/(d.factorial : ℝ)^2≤C*‖f‖^2)
    (M r : ℕ) (v : CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) r) :
    ∑m∈Finset.Icc 1 M,a (m+1)*‖(actualPowerObservationBlock hφ hκ hlower hμ m r).adjoint v‖^2≤C*‖v‖^2 := by
  calc
    _ ≤ ∑m∈Finset.Icc 1 M,a (m+1)*(((m+1).factorial : ℝ)⁻¹^2*
        ∑I,actualAppellEnergy (potentialMeasure φ) ((v : OrderedTensorField φ r) I) (m+1)) := by
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_left
        (actual_repeated_observation_block_adjoint_sq_le hφ hκ hlower hμ m r v)
        (ha (m+1))
    _ = ∑I,∑m∈Finset.Icc 1 M,a (m+1)*
        actualAppellEnergy (potentialMeasure φ) ((v : OrderedTensorField φ r) I) (m+1)/
          ((m+1).factorial : ℝ)^2 := by
      simp_rw [←mul_assoc,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro m hm
      simp only [div_eq_mul_inv,inv_pow]
      ring
    _ = ∑I,∑d∈Finset.Icc 2 (M+1),a d*
        actualAppellEnergy (potentialMeasure φ) ((v : OrderedTensorField φ r) I) d/(d.factorial : ℝ)^2 := by
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_bij (fun m _ => m+1)
      · intro m hm
        simp only [Finset.mem_Icc] at hm ⊢
        omega
      · intro a ha b hb he
        omega
      · intro d hd
        simp only [Finset.mem_Icc] at hd
        refine ⟨d-1,?_,?_⟩
        · simp only [Finset.mem_Icc]
          omega
        · omega
      · intro m hm
        rfl
    _ ≤ ∑I,C*‖(v : OrderedTensorField φ r) I‖^2 :=
      Finset.sum_le_sum (fun I _ => hcoupled (M+1) ((v : OrderedTensorField φ r) I))
    _ = _ := by
      rw [←Finset.mul_sum,←PiLp.norm_sq_eq_of_L2]
      rfl

/-- Coupled scalar Appell control gives the genuine joint observability
bound on the entire graded tensor Hilbert space, with identical constants. -/
theorem actual_general_graded_observability {C : ℝ} (a : ℕ→ℝ) (ha : ∀ d, 0≤a d) (hC : 0≤C)
    (hcoupled : ∀ (N : ℕ) (f : Lp ℝ 2 (potentialMeasure φ)),
      ∑d∈Finset.Icc 2 N,a d*actualAppellEnergy (potentialMeasure φ) f d/(d.factorial : ℝ)^2≤C*‖f‖^2)
    (M : ℕ) (f : GradedCenteredTensorHilbert hφ) :
    ∑m∈Finset.Icc 1 M,a (m+1)*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
      (((gradedTensorIntegration hφ hκ hlower).adjoint^m) f)‖^2≤C*‖f‖^2 := by
  have hb := weighted_joint_adjoint_observation_le_of_blocks
    (centeredTensorIntegration hφ hκ hlower) (constantTensorIntegration hφ hκ hlower)
    (Real.sqrt_nonneg _) (centeredTensorIntegration_opNorm_le hφ hκ hlower) zero_le_one
    (constantTensorIntegration_opNorm_le_one hφ hκ hlower hμ.isotropic)
    (Finset.Icc 1 M) (fun m => a (m+1)) hC
    (fun r v => actual_general_observation_block_le hφ hκ hlower hμ a ha hcoupled M r v) f
  change ∑m∈Finset.Icc 1 M,a (m+1)*
    ‖(((gradedTensorIntegration hφ hκ hlower)^m).comp
      (gradedConstantIntegration hφ hκ hlower hμ.isotropic)).adjoint f‖^2≤C*‖f‖^2 at hb
  simpa only [adjoint_comp,AdjointOrbitRecurrence.adjoint_pow,ContinuousLinearMap.comp_apply] using hb


/-- A weight floor turns a weighted all-test budget into a geometric budget. -/
theorem raw_geometric_budget_of_floor {K C τ : ℝ} (hK : 0<K) (hτ : 0<τ)
    (t : ℕ→ℝ) (ht : ∀ d, 2≤d → τ≤t d)
    (hraw : ∀ (N : ℕ) (f : Lp ℝ 2 (potentialMeasure φ)),
      ∑ d∈Finset.Icc 2 N,t d*K⁻¹^d*actualAppellEnergy (potentialMeasure φ) f d/(d.factorial : ℝ)^2≤C*‖f‖^2)
    (N : ℕ) (f : Lp ℝ 2 (potentialMeasure φ)) :
    ∑ d∈Finset.Icc 2 N,K⁻¹^d*actualAppellEnergy (potentialMeasure φ) f d/(d.factorial : ℝ)^2≤(C/τ)*‖f‖^2 := by
  have hb : τ*(∑ d∈Finset.Icc 2 N,K⁻¹^d*actualAppellEnergy (potentialMeasure φ) f d/(d.factorial : ℝ)^2)≤C*‖f‖^2 := by
    calc
      _=∑ d∈Finset.Icc 2 N,τ*(K⁻¹^d*actualAppellEnergy (potentialMeasure φ) f d/(d.factorial : ℝ)^2) := by rw [Finset.mul_sum]
      _≤∑ d∈Finset.Icc 2 N,t d*K⁻¹^d*actualAppellEnergy (potentialMeasure φ) f d/(d.factorial : ℝ)^2 := by
        apply Finset.sum_le_sum
        intro d hd
        have hh := mul_le_mul_of_nonneg_right (ht d (Finset.mem_Icc.mp hd).1)
          (div_nonneg (mul_nonneg (pow_nonneg (inv_nonneg.mpr hK.le) d)
            (actualAppellEnergy_nonneg (potentialMeasure φ) f d)) (sq_nonneg (d.factorial : ℝ)))
        convert hh using 1 <;> ring
      _≤_ := hraw N f
  have hh := (le_div_iff₀ hτ).mpr (by simpa only [mul_comm] using hb)
  convert hh using 1 <;> ring

include hμ in
theorem actual_general_adjoint_power_envelope {K C τ : ℝ}
    (hK : 0<K) (hC : 0≤C) (hτ : 0<τ) (t : ℕ→ℝ) (ht : ∀ d, 2≤d → τ≤t d)
    (hraw : ∀ (N : ℕ) (f : Lp ℝ 2 (potentialMeasure φ)),
      ∑ d∈Finset.Icc 2 N,t d*K⁻¹^d*actualAppellEnergy (potentialMeasure φ) f d/(d.factorial : ℝ)^2≤C*‖f‖^2) :
    ∀ rho : ℝ, 1 < rho → ∃ M : ℝ, ∀ m,
      ‖(gradedTensorIntegration hφ hκ hlower).adjoint^m‖^2 ≤ M*(K*rho)^m := by
  let R := gradedTensorIntegration hφ hκ hlower
  let L := gradedConstantIntegration hφ hκ hlower hμ.isotropic
  have hbudget : jointObservationBudget R L K (C/τ) := by
    intro N f
    exact actual_joint_graded_observability hφ hκ hlower hμ hK (div_nonneg hC hτ.le)
      (raw_geometric_budget_of_floor hK hτ t ht hraw) N f
  rcases subsingleton_or_nontrivial (RealHilbertComplexification (GradedCenteredTensorHilbert hφ)) with hsub | hn
  · intro rho hrho
    refine ⟨0,fun m => ?_⟩
    have he : (KLSBelow25.RealHilbertComplexification.extend R).adjoint^m=0 := Subsingleton.elim _ _
    have hz : ‖R.adjoint^m‖=0 := by
      simpa only [←extend_adjoint,←extend_pow,norm_extend,norm_zero] using congrArg norm he
    change ‖R.adjoint^m‖^2 ≤ _
    rw [hz]
    simp
  · have hcomparison := actual_graded_rational_comparison hφ hκ hlower hμ.isotropic
      (actual_tensor_curvature_comparison hφ hκ hlower)
    have hcomp := rationalIntegrationComparison_extend R L hκ.le hcomparison
    have hU := canonicalIntegrationResolvent_inverse (KLSBelow25.RealHilbertComplexification.extend R) (KLSBelow25.RealHilbertComplexification.extend L) hκ.le
    have hscalar := scalar_curvature_comparison_of_resolvent (KLSBelow25.RealHilbertComplexification.extend R) (KLSBelow25.RealHilbertComplexification.extend L)
      (canonicalIntegrationResolvent (KLSBelow25.RealHilbertComplexification.extend R) (KLSBelow25.RealHilbertComplexification.extend L) κ) hκ hU hcomp
    have hbudgetC := jointObservationBudget_extend R L hbudget
    have hspec : spectralRadius ℂ (KLSBelow25.RealHilbertComplexification.extend R).adjoint≤ENNReal.ofReal (Real.sqrt K) := by
      apply spectralRadius_le_of_scalar_comparison (KLSBelow25.RealHilbertComplexification.extend R).adjoint (KLSBelow25.RealHilbertComplexification.extend L).adjoint hκ hK 1
      · simpa only [adjoint_adjoint] using hscalar
      · intro m hm
        calc
          ‖(KLSBelow25.RealHilbertComplexification.extend L).adjoint.comp ((KLSBelow25.RealHilbertComplexification.extend R).adjoint^m)‖^2≤(C/τ)*K^(m+1) :=
            observation_norm_sq_le_of_joint_budget (KLSBelow25.RealHilbertComplexification.extend R) (KLSBelow25.RealHilbertComplexification.extend L) hK
              (div_nonneg hC hτ.le) hbudgetC m hm
          _ = ((C/τ)*K)*K^m := by rw [pow_succ]; ring
    intro rho hrho
    obtain ⟨M,hM⟩ := squared_power_envelope_of_spectralRadius_le
      (KLSBelow25.RealHilbertComplexification.extend R).adjoint hK hspec rho hrho
    refine ⟨M,fun m => ?_⟩
    simpa only [←extend_adjoint,←extend_pow,norm_extend] using hM m

end KLSConstantImprovement.GeneralWeightedObservation
#print axioms KLSConstantImprovement.GeneralWeightedObservation.actual_general_graded_observability
#print axioms KLSConstantImprovement.GeneralWeightedObservation.raw_geometric_budget_of_floor
#print axioms KLSConstantImprovement.GeneralWeightedObservation.actual_general_adjoint_power_envelope

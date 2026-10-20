import ActualIndividualObservationCaps
import ActualCreationCubicSeed24Cap

/-! Supporting-line versions of the genuine correlated quadratic/cubic
Appell seed pass to the actual graded observations.  Both scalar energies
are evaluated on the same test before taking any tensor or graded sum. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open MeasureTheory InnerProductSpace Set Matrix ContinuousLinearMap
open scoped ContDiff BigOperators RealInnerProductSpace ENNReal

namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration

theorem actual_correlated_cubic_supporting_cap {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    {a b H : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (hshape : ∀ u ∈ Icc (0 : ℝ) 1,
      2*a*u+b*CreationSeed24.B*CreationSeed24.seedPhi u ≤ H)
    (f : Lp ℝ 2 μ) :
    (a/4)*actualAppellEnergy μ f 2+(b/36)*actualAppellEnergy μ f 3 ≤ H*‖f‖^2 := by
  by_cases hf : f = 0
  · subst f
    simp only [actualAppellEnergy_eq_norm_sq]
    change (a/4)*‖fullClassAppellLinearMap hμ.logConcave 2 0‖^2+
      (b/36)*‖fullClassAppellLinearMap hμ.logConcave 3 0‖^2 ≤ H*‖(0 : Lp ℝ 2 μ)‖^2
    simp
  have hn : 0 < ‖f‖ := norm_pos_iff.mpr hf
  let g : Lp ℝ 2 μ := ‖f‖⁻¹ • f
  have hg : ‖g‖ = 1 := norm_smul_inv_norm hf
  have he2 := actualAppellEnergy_two_le_eight_norm_sq hμ g
  rw [hg, one_pow, mul_one] at he2
  let u : ℝ := actualAppellEnergy μ g 2/8
  have hu : u ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (actualAppellEnergy_nonneg _ _ _) (by norm_num),
      (div_le_one (by norm_num : (0 : ℝ) < 8)).mpr he2⟩
  have hseed := actual_appell_joint_cubic_seed_creation24 hμ g hg
  have hsupport := hshape u hu
  have hunit : (a/4)*actualAppellEnergy μ g 2+
      (b/36)*actualAppellEnergy μ g 3 ≤ H := by
    have hmul := mul_le_mul_of_nonneg_left hseed (div_nonneg hb (by norm_num : (0:ℝ)≤36))
    dsimp only [u] at hsupport
    nlinarith
  have hscale (d : ℕ) : actualAppellEnergy μ f d = ‖f‖^2*actualAppellEnergy μ g d := by
    dsimp only [g]
    rw [actualAppellEnergy_smul_Lp hμ.logConcave]
    field_simp [hn.ne']
  rw [hscale 2, hscale 3]
  calc
    _ = ‖f‖^2*((a/4)*actualAppellEnergy μ g 2+(b/36)*actualAppellEnergy μ g 3) := by ring
    _ ≤ ‖f‖^2*H := mul_le_mul_of_nonneg_left hunit (sq_nonneg _)
    _ = _ := by ring

end KLS.DeterministicBridgeNext

namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLSBelow25 KLSBelow25.GradedHilbert
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
variable [IsProbabilityMeasure (potentialMeasure φ)]
variable (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (v : Fin n → ℝ), κ*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ x *ᵥ v))
  (hμ : admissibleMeasure (potentialMeasure φ))

theorem actual_two_graded_observations_combined_sq_le {a b H : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hH : 0 ≤ H)
    (hscalar : ∀ f : Lp ℝ 2 (potentialMeasure φ),
      (a/4)*actualAppellEnergy (potentialMeasure φ) f 2+
        (b/36)*actualAppellEnergy (potentialMeasure φ) f 3 ≤ H*‖f‖^2)
    (f : GradedCenteredTensorHilbert hφ) :
    a*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
      (((gradedTensorIntegration hφ hκ hlower).adjoint^1) f)‖^2+
    b*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
      (((gradedTensorIntegration hφ hκ hlower).adjoint^2) f)‖^2 ≤ H*‖f‖^2 := by
  have hblock (r : ℕ) (v : CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) r) :
      a*‖(actualPowerObservationBlock hφ hκ hlower hμ 1 r).adjoint v‖^2+
      b*‖(actualPowerObservationBlock hφ hκ hlower hμ 2 r).adjoint v‖^2 ≤ H*‖v‖^2 := by
    have h1 := actual_repeated_observation_block_adjoint_sq_le hφ hκ hlower hμ 1 r v
    have h2 := actual_repeated_observation_block_adjoint_sq_le hφ hκ hlower hμ 2 r v
    norm_num only [Nat.add, Nat.factorial, Nat.cast_ofNat, inv_pow] at h1 h2
    calc
      _ ≤ (a/4)*∑ I, actualAppellEnergy (potentialMeasure φ) ((v : OrderedTensorField φ r) I) 2+
          (b/36)*∑ I, actualAppellEnergy (potentialMeasure φ) ((v : OrderedTensorField φ r) I) 3 := by
        have ha1 := mul_le_mul_of_nonneg_left h1 ha
        have hb2 := mul_le_mul_of_nonneg_left h2 hb
        nlinarith
      _ = ∑ I, ((a/4)*actualAppellEnergy (potentialMeasure φ) ((v : OrderedTensorField φ r) I) 2+
          (b/36)*actualAppellEnergy (potentialMeasure φ) ((v : OrderedTensorField φ r) I) 3) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ ∑ I, H*‖(v : OrderedTensorField φ r) I‖^2 :=
        Finset.sum_le_sum (fun I _ => hscalar ((v : OrderedTensorField φ r) I))
      _ = _ := by
        rw [←Finset.mul_sum, ←PiLp.norm_sq_eq_of_L2]
        rfl
  have hx := weighted_joint_adjoint_observation_le_of_blocks
    (centeredTensorIntegration hφ hκ hlower) (constantTensorIntegration hφ hκ hlower)
    (Real.sqrt_nonneg _) (centeredTensorIntegration_opNorm_le hφ hκ hlower) zero_le_one
    (constantTensorIntegration_opNorm_le_one hφ hκ hlower hμ.isotropic)
    ({1,2} : Finset ℕ) (fun d => if d=1 then a else b) hH
    (fun r v => by simpa only [Finset.sum_insert, Finset.mem_singleton,
      show ¬(1 : ℕ)=2 by omega, not_false_eq_true, Finset.sum_singleton,
      ite_true, ite_false, show (2 : ℕ)≠1 by omega, actualPowerObservationBlock] using hblock r v) f
  simp only [Finset.sum_insert, Finset.mem_singleton, show ¬(1 : ℕ)=2 by omega,
    not_false_eq_true, Finset.sum_singleton, ite_true, ite_false,
    show (2 : ℕ)≠1 by omega] at hx
  change a*‖(((gradedTensorIntegration hφ hκ hlower)^1).comp
      (gradedConstantIntegration hφ hκ hlower hμ.isotropic)).adjoint f‖^2+
    b*‖(((gradedTensorIntegration hφ hκ hlower)^2).comp
      (gradedConstantIntegration hφ hκ hlower hμ.isotropic)).adjoint f‖^2 ≤ _ at hx
  simpa only [adjoint_comp, AdjointOrbitRecurrence.adjoint_pow, ContinuousLinearMap.comp_apply] using hx

theorem actual_correlated_cubic_graded_supporting_cap {a b H : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hH : 0 ≤ H)
    (hshape : ∀ u ∈ Icc (0 : ℝ) 1,
      2*a*u+b*CreationSeed24.B*CreationSeed24.seedPhi u ≤ H)
    (f : GradedCenteredTensorHilbert hφ) :
    a*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
      (((gradedTensorIntegration hφ hκ hlower).adjoint^1) f)‖^2+
    b*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
      (((gradedTensorIntegration hφ hκ hlower).adjoint^2) f)‖^2 ≤ H*‖f‖^2 :=
  actual_two_graded_observations_combined_sq_le hφ hκ hlower hμ ha hb hH
    (actual_correlated_cubic_supporting_cap hμ ha hb hshape) f

end KLS.DeterministicBridgeIntegration

#print axioms KLS.DeterministicBridgeNext.actual_correlated_cubic_supporting_cap
#print axioms KLS.DeterministicBridgeIntegration.actual_two_graded_observations_combined_sq_le
#print axioms KLS.DeterministicBridgeIntegration.actual_correlated_cubic_graded_supporting_cap

import ActualCorrelatedCubicObservationCaps
import KLSConstantImprovement.ActualCreationCubicSeed2388Cap

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

theorem actual_correlated_cubic_supporting_cap_creation2388 {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    {a b H : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (hshape : ∀ u ∈ Icc (0 : ℝ) 1,
      2*a*u+b*CreationSeed2388.B*CreationSeed2388.seedPhi u ≤ H)
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
  have hseed := actual_appell_joint_cubic_seed_creation2388 hμ g hg
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

theorem actual_correlated_cubic_graded_supporting_cap_creation2388 {a b H : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hH : 0 ≤ H)
    (hshape : ∀ u ∈ Icc (0 : ℝ) 1,
      2*a*u+b*CreationSeed2388.B*CreationSeed2388.seedPhi u ≤ H)
    (f : GradedCenteredTensorHilbert hφ) :
    a*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
      (((gradedTensorIntegration hφ hκ hlower).adjoint^1) f)‖^2+
    b*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
      (((gradedTensorIntegration hφ hκ hlower).adjoint^2) f)‖^2 ≤ H*‖f‖^2 :=
  actual_two_graded_observations_combined_sq_le hφ hκ hlower hμ ha hb hH
    (actual_correlated_cubic_supporting_cap_creation2388 hμ ha hb hshape) f

end KLS.DeterministicBridgeIntegration

#print axioms KLS.DeterministicBridgeNext.actual_correlated_cubic_supporting_cap_creation2388
#print axioms KLS.DeterministicBridgeIntegration.actual_correlated_cubic_graded_supporting_cap_creation2388

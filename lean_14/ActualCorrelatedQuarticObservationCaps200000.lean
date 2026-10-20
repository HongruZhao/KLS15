import ActualCorrelatedCubicObservationCaps239
import ActualQuarticJointSeed200000

/-! Three actual Appell energies are bounded on the same scalar test before
any tensor-coordinate or graded-Hilbert sum.  The shape premise is a scalar
support inequality on the two genuine adjacent curved seed constraints. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open MeasureTheory InnerProductSpace Set Matrix ContinuousLinearMap
open scoped ContDiff BigOperators RealInnerProductSpace ENNReal
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration

theorem actual_correlated_quartic_supporting_cap_creation200000 {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    {a b c H : ℝ} (_ha : 0 ≤ a) (_hb : 0 ≤ b) (hc : 0 ≤ c)
    (hshape : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      v ≤ CreationSeed239.seedPhi u →
      2*a*u+b*CreationSeed239.B*v+(c/576)*200000*
        QuarticCreation200000.seedPhi v ≤ H)
    (f : Lp ℝ 2 μ) :
    (a/4)*actualAppellEnergy μ f 2+(b/36)*actualAppellEnergy μ f 3+
      (c/576)*actualAppellEnergy μ f 4 ≤ H*‖f‖^2 := by
  by_cases hf : f = 0
  · subst f
    simp only [actualAppellEnergy_eq_norm_sq]
    change (a/4)*‖fullClassAppellLinearMap hμ.logConcave 2 0‖^2+
      (b/36)*‖fullClassAppellLinearMap hμ.logConcave 3 0‖^2+
      (c/576)*‖fullClassAppellLinearMap hμ.logConcave 4 0‖^2 ≤ H*‖(0 : Lp ℝ 2 μ)‖^2
    simp
  have hn : 0 < ‖f‖ := norm_pos_iff.mpr hf
  let g : Lp ℝ 2 μ := ‖f‖⁻¹ • f
  have hg : ‖g‖ = 1 := norm_smul_inv_norm hf
  have he2 := actualAppellEnergy_two_le_eight_norm_sq hμ g
  have he3 := actual_appell_energy_three_creation239_le_norm_sq hμ g
  rw [hg, one_pow, mul_one] at he2 he3
  let u : ℝ := actualAppellEnergy μ g 2/8
  let v : ℝ := actualAppellEnergy μ g 3/quarticCreationPrior239
  have hu : u ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (actualAppellEnergy_nonneg _ _ _) (by norm_num),
      (div_le_one (by norm_num : (0 : ℝ) < 8)).mpr he2⟩
  have hv : v ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (actualAppellEnergy_nonneg _ _ _) quarticCreationPrior239_positive.le,
      (div_le_one quarticCreationPrior239_positive).mpr he3⟩
  have hseed3 := actual_appell_joint_cubic_seed_creation239 hμ g hg
  have hcurve : v ≤ CreationSeed239.seedPhi u := by
    apply (div_le_iff₀ quarticCreationPrior239_positive).2
    simpa only [u, quarticCreationPrior239, mul_assoc, mul_comm, mul_left_comm] using hseed3
  have hseed4 := actual_appell_joint_quartic_seed_creation200000 hμ g hg
  have hsupport := hshape u hu v hv hcurve
  have hunit : (a/4)*actualAppellEnergy μ g 2+
      (b/36)*actualAppellEnergy μ g 3+(c/576)*actualAppellEnergy μ g 4 ≤ H := by
    have hmul := mul_le_mul_of_nonneg_left hseed4
      (div_nonneg hc (by norm_num : (0 : ℝ) ≤ 576))
    dsimp only [u, v, quarticCreationPrior239] at hsupport
    norm_num only [CreationSeed239.B, quarticCreationPrior239] at hsupport hmul ⊢
    nlinarith
  have hscale (d : ℕ) : actualAppellEnergy μ f d = ‖f‖^2*actualAppellEnergy μ g d := by
    dsimp only [g]
    rw [actualAppellEnergy_smul_Lp hμ.logConcave]
    field_simp [hn.ne']
  rw [hscale 2, hscale 3, hscale 4]
  calc
    _ = ‖f‖^2*((a/4)*actualAppellEnergy μ g 2+
      (b/36)*actualAppellEnergy μ g 3+(c/576)*actualAppellEnergy μ g 4) := by ring
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

theorem actual_three_graded_observations_combined_sq_le {a b c H : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hH : 0 ≤ H)
    (hscalar : ∀ f : Lp ℝ 2 (potentialMeasure φ),
      (a/4)*actualAppellEnergy (potentialMeasure φ) f 2+
        (b/36)*actualAppellEnergy (potentialMeasure φ) f 3+
        (c/576)*actualAppellEnergy (potentialMeasure φ) f 4 ≤ H*‖f‖^2)
    (f : GradedCenteredTensorHilbert hφ) :
    a*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
      (((gradedTensorIntegration hφ hκ hlower).adjoint^1) f)‖^2+
    b*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
      (((gradedTensorIntegration hφ hκ hlower).adjoint^2) f)‖^2+
    c*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
      (((gradedTensorIntegration hφ hκ hlower).adjoint^3) f)‖^2 ≤ H*‖f‖^2 := by
  have hblock (r : ℕ) (v : CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) r) :
      a*‖(actualPowerObservationBlock hφ hκ hlower hμ 1 r).adjoint v‖^2+
      b*‖(actualPowerObservationBlock hφ hκ hlower hμ 2 r).adjoint v‖^2+
      c*‖(actualPowerObservationBlock hφ hκ hlower hμ 3 r).adjoint v‖^2 ≤ H*‖v‖^2 := by
    have h1 := actual_repeated_observation_block_adjoint_sq_le hφ hκ hlower hμ 1 r v
    have h2 := actual_repeated_observation_block_adjoint_sq_le hφ hκ hlower hμ 2 r v
    have h3 := actual_repeated_observation_block_adjoint_sq_le hφ hκ hlower hμ 3 r v
    norm_num only [Nat.add, Nat.factorial, Nat.cast_ofNat, inv_pow] at h1 h2 h3
    calc
      _ ≤ (a/4)*∑ I, actualAppellEnergy (potentialMeasure φ) ((v : OrderedTensorField φ r) I) 2+
          (b/36)*∑ I, actualAppellEnergy (potentialMeasure φ) ((v : OrderedTensorField φ r) I) 3+
          (c/576)*∑ I, actualAppellEnergy (potentialMeasure φ) ((v : OrderedTensorField φ r) I) 4 := by
        have ha1 := mul_le_mul_of_nonneg_left h1 ha
        have hb2 := mul_le_mul_of_nonneg_left h2 hb
        have hc3 := mul_le_mul_of_nonneg_left h3 hc
        nlinarith
      _ = ∑ I, ((a/4)*actualAppellEnergy (potentialMeasure φ) ((v : OrderedTensorField φ r) I) 2+
          (b/36)*actualAppellEnergy (potentialMeasure φ) ((v : OrderedTensorField φ r) I) 3+
          (c/576)*actualAppellEnergy (potentialMeasure φ) ((v : OrderedTensorField φ r) I) 4) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ ∑ I, H*‖(v : OrderedTensorField φ r) I‖^2 :=
        Finset.sum_le_sum (fun I _ => hscalar ((v : OrderedTensorField φ r) I))
      _ = _ := by
        rw [←Finset.mul_sum, ←PiLp.norm_sq_eq_of_L2]
        rfl
  have hx := weighted_joint_adjoint_observation_le_of_blocks
    (centeredTensorIntegration hφ hκ hlower) (constantTensorIntegration hφ hκ hlower)
    (Real.sqrt_nonneg _) (centeredTensorIntegration_opNorm_le hφ hκ hlower) zero_le_one
    (constantTensorIntegration_opNorm_le_one hφ hκ hlower hμ.isotropic)
    ({1,2,3} : Finset ℕ) (fun d => if d=1 then a else if d=2 then b else c) hH
    (fun r v => by simpa only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
      show ¬(1 : ℕ)=2 by omega, show ¬(1 : ℕ)=3 by omega,
      show ¬(2 : ℕ)=3 by omega, not_false_eq_true, Finset.sum_singleton,
      ite_true, ite_false, show (2 : ℕ)≠1 by omega,
      show (3 : ℕ)≠1 by omega, show (3 : ℕ)≠2 by omega,
      false_or, add_assoc, actualPowerObservationBlock] using hblock r v) f
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    show ¬(1 : ℕ)=2 by omega, show ¬(1 : ℕ)=3 by omega,
    show ¬(2 : ℕ)=3 by omega, not_false_eq_true, Finset.sum_singleton,
    ite_true, ite_false, show (2 : ℕ)≠1 by omega,
    show (3 : ℕ)≠1 by omega, show (3 : ℕ)≠2 by omega, false_or, ←add_assoc] at hx
  change a*‖(((gradedTensorIntegration hφ hκ hlower)^1).comp
      (gradedConstantIntegration hφ hκ hlower hμ.isotropic)).adjoint f‖^2+
    b*‖(((gradedTensorIntegration hφ hκ hlower)^2).comp
      (gradedConstantIntegration hφ hκ hlower hμ.isotropic)).adjoint f‖^2+
    c*‖(((gradedTensorIntegration hφ hκ hlower)^3).comp
      (gradedConstantIntegration hφ hκ hlower hμ.isotropic)).adjoint f‖^2 ≤ _ at hx
  simpa only [adjoint_comp, AdjointOrbitRecurrence.adjoint_pow, ContinuousLinearMap.comp_apply] using hx


theorem actual_correlated_quartic_graded_supporting_cap_creation200000 {a b c H : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hH : 0 ≤ H)
    (hshape : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      v ≤ CreationSeed239.seedPhi u →
      2*a*u+b*CreationSeed239.B*v+(c/576)*200000*
        QuarticCreation200000.seedPhi v ≤ H)
    (f : GradedCenteredTensorHilbert hφ) :
    a*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
      (((gradedTensorIntegration hφ hκ hlower).adjoint^1) f)‖^2+
    b*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
      (((gradedTensorIntegration hφ hκ hlower).adjoint^2) f)‖^2+
    c*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
      (((gradedTensorIntegration hφ hκ hlower).adjoint^3) f)‖^2 ≤ H*‖f‖^2 :=
  actual_three_graded_observations_combined_sq_le hφ hκ hlower hμ ha hb hc hH
    (actual_correlated_quartic_supporting_cap_creation200000 hμ ha hb hc hshape) f

/-- The genuine fourth scalar energy gives the third actual observation,
with the exact 4! squared normalization, uniformly over every free tensor grade. -/
theorem actual_fourth_graded_observation_creation200000_sq_le
    (f : GradedCenteredTensorHilbert hφ) :
    ‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
      (((gradedTensorIntegration hφ hκ hlower).adjoint^3) f)‖^2 ≤
        (200000/576 : ℝ)*‖f‖^2 := by
  have hh := actual_individual_graded_observation_sq_le hφ hκ hlower hμ 3
    (by norm_num : (0 : ℝ) ≤ 200000)
    (actual_appell_energy_four_creation200000_le_norm_sq hμ) f
  norm_num only [Nat.add, Nat.factorial, Nat.cast_ofNat, inv_pow] at hh
  convert hh using 1
  ring

/-- Normalization used by the adjoint-orbit energy recurrence. -/
theorem actual_normalized_fourth_graded_observation_creation200000_sq_le
    {K : ℝ} (hK : 0 < K) (f : GradedCenteredTensorHilbert hφ) :
    K⁻¹^4*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
      (((gradedTensorIntegration hφ hκ hlower).adjoint^3) f)‖^2 ≤
        (200000/(576*K^4) : ℝ)*‖f‖^2 := by
  have hh := mul_le_mul_of_nonneg_left
    (actual_fourth_graded_observation_creation200000_sq_le hφ hκ hlower hμ f)
    (pow_nonneg (inv_nonneg.mpr hK.le) 4)
  convert hh using 1
  simp only [inv_pow, div_eq_mul_inv]
  ring

/-- The three scalar seed constraints provide one normalized supporting cap,
with the same input vector throughout and no free-tensor-rank factor. -/
theorem actual_normalized_correlated_quartic_graded_supporting_cap_creation200000
    {K a b c H : ℝ} (hK : 0 < K) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hH : 0 ≤ H)
    (hshape : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      v ≤ CreationSeed239.seedPhi u →
      2*(a/K^2)*u+(b/K^3)*CreationSeed239.B*v+
        (200000*c/(576*K^4))*QuarticCreation200000.seedPhi v ≤ H)
    (f : GradedCenteredTensorHilbert hφ) :
    a*(K⁻¹^2*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
      (((gradedTensorIntegration hφ hκ hlower).adjoint^1) f)‖^2)+
    b*(K⁻¹^3*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
      (((gradedTensorIntegration hφ hκ hlower).adjoint^2) f)‖^2)+
    c*(K⁻¹^4*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
      (((gradedTensorIntegration hφ hκ hlower).adjoint^3) f)‖^2) ≤ H*‖f‖^2 := by
  have hh := actual_correlated_quartic_graded_supporting_cap_creation200000
    hφ hκ hlower hμ (a := a/K^2) (b := b/K^3) (c := c/K^4)
    (div_nonneg ha (sq_nonneg _))
    (div_nonneg hb (pow_nonneg hK.le 3))
    (div_nonneg hc (pow_nonneg hK.le 4)) hH
    (fun u hu v hv hcurve => by
      convert hshape u hu v hv hcurve using 1; ring) f
  convert hh using 1; simp only [inv_pow, div_eq_mul_inv]; ring

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeNext.actual_correlated_quartic_supporting_cap_creation200000
#print axioms KLS.DeterministicBridgeIntegration.actual_three_graded_observations_combined_sq_le
#print axioms KLS.DeterministicBridgeIntegration.actual_correlated_quartic_graded_supporting_cap_creation200000
#print axioms KLS.DeterministicBridgeIntegration.actual_fourth_graded_observation_creation200000_sq_le

#print axioms KLS.DeterministicBridgeIntegration.actual_normalized_fourth_graded_observation_creation200000_sq_le
#print axioms KLS.DeterministicBridgeIntegration.actual_normalized_correlated_quartic_graded_supporting_cap_creation200000

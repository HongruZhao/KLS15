import ActualCreationCenteredCubicSeed239
import ActualSymmetricCubicSeed245Cap
noncomputable section
open MeasureTheory Set
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem actual_appell_energy_three_creation239_le_norm_sq {n:ℕ}
    {μ:Measure (Space n)} [IsProbabilityMeasure μ] (hμ:admissibleMeasure μ)
    (f:Lp ℝ 2 μ) :
    actualAppellEnergy μ f 3 ≤ (36*CreationSeed239.B)*‖f‖^2 := by
  by_cases hf:f=0
  · subst f
    rw [actualAppellEnergy_eq_norm_sq]
    change ‖fullClassAppellLinearMap hμ.logConcave 3 0‖^2≤_
    simp
  have hn:0<‖f‖ := norm_pos_iff.mpr hf
  let g:Lp ℝ 2 μ := ‖f‖⁻¹ • f
  have hg:‖g‖=1 := norm_smul_inv_norm hf
  have hb := actual_appell_joint_cubic_seed_creation239 hμ g hg
  have he2 := actualAppellEnergy_two_le_eight_norm_sq hμ g
  rw [hg,one_pow,mul_one] at he2
  have hu:actualAppellEnergy μ g 2/8∈Icc (0:ℝ) 1 :=
    ⟨div_nonneg (actualAppellEnergy_nonneg _ _ _) (by norm_num),
      (div_le_one (by norm_num : (0:ℝ)<8)).mpr he2⟩
  have hp := (CreationSeed239.seedPhi_range hu).2
  have hcap:actualAppellEnergy μ g 3≤36*CreationSeed239.B := by
    have hpos:0≤36*CreationSeed239.B := by
      have := CreationSeed239.B_positive
      positivity
    exact hb.trans (mul_le_of_le_one_right hpos hp)
  calc
    actualAppellEnergy μ f 3=‖f‖^2*actualAppellEnergy μ g 3 := by
      dsimp only [g]
      rw [actualAppellEnergy_smul_Lp hμ.logConcave]
      field_simp [hn.ne']
    _ ≤ ‖f‖^2*(36*CreationSeed239.B) :=
      mul_le_mul_of_nonneg_left hcap (sq_nonneg _)
    _ = (36*CreationSeed239.B)*‖f‖^2 := by ring

theorem actual_appell_energy_three_creation239_le_integral {n:ℕ}
    {μ:Measure (Space n)} (hμ:admissibleMeasure μ) {f:Space n→ℝ} (hf:MemLp f 2 μ) :
    actualAppellEnergy μ f 3 ≤ (36*CreationSeed239.B)*(∫ x,(f x)^2 ∂μ) := by
  have : IsProbabilityMeasure μ := hμ.isProb
  rw [actualAppellEnergy_eq_toLp_norm_sq hf]
  have hb := actual_appell_energy_three_creation239_le_norm_sq hμ (hf.toLp f)
  rw [actualAppellEnergy_eq_norm_sq] at hb
  calc
    _ ≤ (36*CreationSeed239.B)*‖hf.toLp f‖^2 := hb
    _ = _ := by
      rw [actualLp_norm_sq_eq_integral]
      congr 1
      exact integral_congr_ae (hf.coeFn_toLp.fun_comp (fun t:ℝ => t^2))

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_appell_energy_three_creation239_le_norm_sq
#print axioms KLS.DeterministicBridgeNext.actual_appell_energy_three_creation239_le_integral

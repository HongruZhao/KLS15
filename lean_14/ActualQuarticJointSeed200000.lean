import QuarticCreation200000Scalar
noncomputable section
open MeasureTheory Set
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem actual_appell_joint_quartic_seed_creation200000 {n:ℕ}
    {μ:Measure (Space n)} [IsProbabilityMeasure μ] (hμ:admissibleMeasure μ)
    (f:Lp ℝ 2 μ) (hunit:‖f‖=1) :
    actualAppellEnergy μ f 4 ≤ 200000*QuarticCreation200000.seedPhi
      (actualAppellEnergy μ f 3/quarticCreationPrior239) := by
  let μ₀:ProbabilityMeasure (Space n) := ⟨μ,hμ.isProb⟩
  exact actual_quartic_creation239_joint_unit_bound (μ₀:=μ₀) hμ
    QuarticCreation200000.J_positive QuarticCreation200000.quarticBarrier hμ f hunit

theorem actual_appell_energy_four_creation200000_le_norm_sq {n:ℕ}
    {μ:Measure (Space n)} [IsProbabilityMeasure μ] (hμ:admissibleMeasure μ)
    (f:Lp ℝ 2 μ) : actualAppellEnergy μ f 4 ≤ 200000*‖f‖^2 := by
  by_cases hf:f=0
  · subst f
    rw [actualAppellEnergy_eq_norm_sq]
    change ‖fullClassAppellLinearMap hμ.logConcave 4 0‖^2 ≤ _
    simp
  have hn:0<‖f‖ := norm_pos_iff.mpr hf
  let g:Lp ℝ 2 μ := ‖f‖⁻¹ • f
  have hg:‖g‖=1 := norm_smul_inv_norm hf
  have hb:=actual_appell_joint_quartic_seed_creation200000 hμ g hg
  have he3:=actual_appell_energy_three_creation239_le_norm_sq hμ g
  rw [hg,one_pow,mul_one] at he3
  have hu:actualAppellEnergy μ g 3/quarticCreationPrior239∈Icc (0:ℝ) 1 :=
    ⟨div_nonneg (actualAppellEnergy_nonneg _ _ _) quarticCreationPrior239_positive.le,
      (div_le_one quarticCreationPrior239_positive).mpr he3⟩
  have hp:QuarticCreation200000.seedPhi (actualAppellEnergy μ g 3/quarticCreationPrior239) ≤ 1 :=
    (QuarticCreation200000.seedPhi_range hu).2
  have hcap:actualAppellEnergy μ g 4 ≤ 200000 := by nlinarith
  calc
    actualAppellEnergy μ f 4=‖f‖^2*actualAppellEnergy μ g 4 := by
      dsimp only [g]
      rw [actualAppellEnergy_smul_Lp hμ.logConcave]
      field_simp [hn.ne']
    _ ≤ ‖f‖^2*200000 := mul_le_mul_of_nonneg_left hcap (sq_nonneg _)
    _ = 200000*‖f‖^2 := by ring

theorem actual_appell_energy_four_creation200000_le_integral {n:ℕ}
    {μ:Measure (Space n)} (hμ:admissibleMeasure μ) {f:Space n→ℝ} (hf:MemLp f 2 μ) :
    actualAppellEnergy μ f 4 ≤ 200000*(∫ x,(f x)^2 ∂μ) := by
  have : IsProbabilityMeasure μ := hμ.isProb
  rw [actualAppellEnergy_eq_toLp_norm_sq hf]
  have hb:=actual_appell_energy_four_creation200000_le_norm_sq hμ (hf.toLp f)
  rw [actualAppellEnergy_eq_norm_sq] at hb
  calc
    _ ≤ 200000*‖hf.toLp f‖^2 := hb
    _ = _ := by
      rw [actualLp_norm_sq_eq_integral]
      congr 1
      exact integral_congr_ae (hf.coeFn_toLp.fun_comp (fun t:ℝ => t^2))

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_appell_joint_quartic_seed_creation200000
#print axioms KLS.DeterministicBridgeNext.actual_appell_energy_four_creation200000_le_integral

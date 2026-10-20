import QuarticCreation200000Block0
import QuarticCreation200000ShiftedBlock1
import QuarticCreation200000Block2
import QuarticCreation200000ShiftedBlock3
import QuarticCreation200000ShiftedBlock4
import QuarticCreation200000ShiftedBlock5
import QuarticCreation200000ShiftedBlock6
import QuarticCreation200000ShiftedBlock7
import QuarticCreation200000ShiftedBlock8
import QuarticCreation200000ShiftedBlock9
import QuarticCreation200000Margins
import QuarticCreation200000ZeroEndpoint
noncomputable section
open Set
namespace KLSBelow25.QuarticCreation200000
open KLSBelow25 KLS.DeterministicBridgeNext
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
theorem block0_criterion {t u Z:ℝ} (ht:0<t)
    (hti:t∈Icc (0:ℝ) (563/2000:ℝ)) (heq:u=t^2*(seedV t)^2)
    (hu:u∈Icc (0:ℝ) 1) (hZ:Z∈Icc (0:ℝ) 8)
    (_hcurve:u ≤ CreationSeed239.seedPhi (Z/8)) :
    (-1/((1-t^2)*(-(seedV t*seedSlope t))))*
      (seedAlphaAt t*J/H*(1-t^2)-(44/(1-seedAlphaAt t)-32)*u-
        2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u) >
      29+2*(Real.sqrt (176*H*u)+Real.sqrt (13824*Z))/Real.sqrt (J*(1-t^2)) := by
  have htT:t ≤ seedT := hti.2.trans (by norm_num [seedT])
  have htr:t∈Icc (0:ℝ) seedT := ⟨ht.le,htT⟩
  have hcap:Z ≤ 8*block0Rho := by
    simpa only [block0Rho_eq,mul_one] using hZ.2
  obtain ⟨ha,hb,hc⟩:=radical_majorants_of_rho block0Rho_nonneg block0A_positive.le
    block0C_positive.le hZ.1 hcap block0A_square block0C_square
  apply criterion_of_parameter_margin htr heq hu hZ ha hb hc
  exact variable_margin_of_signs ht htT (block0P_positive hti) (block0Q_positive hti)
    (block0Det_positive hti)

theorem block1_criterion {t u Z:ℝ} (ht:0<t)
    (hti:t∈Icc (563/2000:ℝ) (1689/4000:ℝ)) (heq:u=t^2*(seedV t)^2)
    (hu:u∈Icc (0:ℝ) 1) (hZ:Z∈Icc (0:ℝ) 8)
    (_hcurve:u ≤ CreationSeed239.seedPhi (Z/8)) :
    (-1/((1-t^2)*(-(seedV t*seedSlope t))))*
      (seedAlphaAt t*J/H*(1-t^2)-(44/(1-seedAlphaAt t)-32)*u-
        2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u) >
      29+2*(Real.sqrt (176*H*u)+Real.sqrt (13824*Z))/Real.sqrt (J*(1-t^2)) := by
  have htT:t ≤ seedT := hti.2.trans (by norm_num [seedT])
  have htr:t∈Icc (0:ℝ) seedT := ⟨ht.le,htT⟩
  have hcap:Z ≤ 8*block1Rho := by
    simpa only [block1Rho_eq,mul_one] using hZ.2
  obtain ⟨ha,hb,hc⟩:=radical_majorants_of_rho block1Rho_nonneg block1A_positive.le
    block1C_positive.le hZ.1 hcap block1A_square block1C_square
  apply criterion_of_parameter_margin htr heq hu hZ ha hb hc
  exact variable_margin_of_signs ht htT (block1P_positive hti) (block1Q_positive hti)
    (block1Det_positive hti)

theorem block2_criterion {t u Z:ℝ} (ht:0<t)
    (hti:t∈Icc (1689/4000:ℝ) (3941/8000:ℝ)) (heq:u=t^2*(seedV t)^2)
    (hu:u∈Icc (0:ℝ) 1) (hZ:Z∈Icc (0:ℝ) 8)
    (hcurve:u ≤ CreationSeed239.seedPhi (Z/8)) :
    (-1/((1-t^2)*(-(seedV t*seedSlope t))))*
      (seedAlphaAt t*J/H*(1-t^2)-(44/(1-seedAlphaAt t)-32)*u-
        2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u) >
      29+2*(Real.sqrt (176*H*u)+Real.sqrt (13824*Z))/Real.sqrt (J*(1-t^2)) := by
  have htT:t ≤ seedT := hti.2.trans (by norm_num [seedT])
  have htr:t∈Icc (0:ℝ) seedT := ⟨ht.le,htT⟩
  have hcap:Z ≤ 8*block2Rho := by
    have hl:block2Left∈Icc (0:ℝ) seedT := by norm_num [block2Left,seedT]
    have hm:=parameterValue_monotone hl htr (by simpa only [block2Left] using hti.1)
    have hpar:1-block2Tau^2 ≤ u := by
      have ha:1-block2Tau^2 ≤ parameterValue block2Left := block2Tau_argument
      change parameterValue block2Left ≤ t^2*(seedV t)^2 at hm
      linarith
    have hb:=CreationSeed239.quadratic_energy_le_parameter_cap block2Tau_range hu hZ hcurve hpar
    calc
      Z ≤ 8*(block2Tau^2*(CreationSeed239.seedV block2Tau)^2) := by simpa only [mul_assoc] using hb
      _ = 8*block2Rho := by rw [block2Rho_eq]
  obtain ⟨ha,hb,hc⟩:=radical_majorants_of_rho block2Rho_nonneg block2A_positive.le
    block2C_positive.le hZ.1 hcap block2A_square block2C_square
  apply criterion_of_parameter_margin htr heq hu hZ ha hb hc
  exact variable_margin_of_signs ht htT (block2P_positive hti) (block2Q_positive hti)
    (block2Det_positive hti)

theorem block3_criterion {t u Z:ℝ} (ht:0<t)
    (hti:t∈Icc (3941/8000:ℝ) (563/1000:ℝ)) (heq:u=t^2*(seedV t)^2)
    (hu:u∈Icc (0:ℝ) 1) (hZ:Z∈Icc (0:ℝ) 8)
    (hcurve:u ≤ CreationSeed239.seedPhi (Z/8)) :
    (-1/((1-t^2)*(-(seedV t*seedSlope t))))*
      (seedAlphaAt t*J/H*(1-t^2)-(44/(1-seedAlphaAt t)-32)*u-
        2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u) >
      29+2*(Real.sqrt (176*H*u)+Real.sqrt (13824*Z))/Real.sqrt (J*(1-t^2)) := by
  have htT:t ≤ seedT := hti.2.trans (by norm_num [seedT])
  have htr:t∈Icc (0:ℝ) seedT := ⟨ht.le,htT⟩
  have hcap:Z ≤ 8*block3Rho := by
    have hl:block3Left∈Icc (0:ℝ) seedT := by norm_num [block3Left,seedT]
    have hm:=parameterValue_monotone hl htr (by simpa only [block3Left] using hti.1)
    have hpar:1-block3Tau^2 ≤ u := by
      have ha:1-block3Tau^2 ≤ parameterValue block3Left := block3Tau_argument
      change parameterValue block3Left ≤ t^2*(seedV t)^2 at hm
      linarith
    have hb:=CreationSeed239.quadratic_energy_le_parameter_cap block3Tau_range hu hZ hcurve hpar
    calc
      Z ≤ 8*(block3Tau^2*(CreationSeed239.seedV block3Tau)^2) := by simpa only [mul_assoc] using hb
      _ = 8*block3Rho := by rw [block3Rho_eq]
  obtain ⟨ha,hb,hc⟩:=radical_majorants_of_rho block3Rho_nonneg block3A_positive.le
    block3C_positive.le hZ.1 hcap block3A_square block3C_square
  apply criterion_of_parameter_margin htr heq hu hZ ha hb hc
  exact variable_margin_of_signs ht htT (block3P_positive hti) (block3Q_positive hti)
    (block3Det_positive hti)

theorem block4_criterion {t u Z:ℝ} (ht:0<t)
    (hti:t∈Icc (563/1000:ℝ) (11749/20000:ℝ)) (heq:u=t^2*(seedV t)^2)
    (hu:u∈Icc (0:ℝ) 1) (hZ:Z∈Icc (0:ℝ) 8)
    (hcurve:u ≤ CreationSeed239.seedPhi (Z/8)) :
    (-1/((1-t^2)*(-(seedV t*seedSlope t))))*
      ((1/2:ℝ)*J/H*(1-t^2)-(44/(1-(1/2:ℝ))-32)*u-
        2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u) >
      29+2*(Real.sqrt (176*H*u)+Real.sqrt (13824*Z))/Real.sqrt (J*(1-t^2)) := by
  have htT:t ≤ seedT := hti.2.trans (by norm_num [seedT])
  have htr:t∈Icc (0:ℝ) seedT := ⟨ht.le,htT⟩
  have hcap:Z ≤ 8*block4Rho := by
    have hl:block4Left∈Icc (0:ℝ) seedT := by norm_num [block4Left,seedT]
    have hm:=parameterValue_monotone hl htr (by simpa only [block4Left] using hti.1)
    have hpar:1-block4Tau^2 ≤ u := by
      have ha:1-block4Tau^2 ≤ parameterValue block4Left := block4Tau_argument
      change parameterValue block4Left ≤ t^2*(seedV t)^2 at hm
      linarith
    have hb:=CreationSeed239.quadratic_energy_le_parameter_cap block4Tau_range hu hZ hcurve hpar
    calc
      Z ≤ 8*(block4Tau^2*(CreationSeed239.seedV block4Tau)^2) := by simpa only [mul_assoc] using hb
      _ = 8*block4Rho := by rw [block4Rho_eq]
  obtain ⟨ha,hb,hc⟩:=radical_majorants_of_rho block4Rho_nonneg block4A_positive.le
    block4C_positive.le hZ.1 hcap block4A_square block4C_square
  apply criterion_of_parameter_margin htr heq hu hZ ha hb hc
  exact half_margin_of_signs ht.le htT (block4P_positive hti) (block4Q_positive hti)
    (block4Det_positive hti)

theorem block5_criterion {t u Z:ℝ} (ht:0<t)
    (hti:t∈Icc (11749/20000:ℝ) (6119/10000:ℝ)) (heq:u=t^2*(seedV t)^2)
    (hu:u∈Icc (0:ℝ) 1) (hZ:Z∈Icc (0:ℝ) 8)
    (hcurve:u ≤ CreationSeed239.seedPhi (Z/8)) :
    (-1/((1-t^2)*(-(seedV t*seedSlope t))))*
      ((1/2:ℝ)*J/H*(1-t^2)-(44/(1-(1/2:ℝ))-32)*u-
        2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u) >
      29+2*(Real.sqrt (176*H*u)+Real.sqrt (13824*Z))/Real.sqrt (J*(1-t^2)) := by
  have htT:t ≤ seedT := hti.2.trans (by norm_num [seedT])
  have htr:t∈Icc (0:ℝ) seedT := ⟨ht.le,htT⟩
  have hcap:Z ≤ 8*block5Rho := by
    have hl:block5Left∈Icc (0:ℝ) seedT := by norm_num [block5Left,seedT]
    have hm:=parameterValue_monotone hl htr (by simpa only [block5Left] using hti.1)
    have hpar:1-block5Tau^2 ≤ u := by
      have ha:1-block5Tau^2 ≤ parameterValue block5Left := block5Tau_argument
      change parameterValue block5Left ≤ t^2*(seedV t)^2 at hm
      linarith
    have hb:=CreationSeed239.quadratic_energy_le_parameter_cap block5Tau_range hu hZ hcurve hpar
    calc
      Z ≤ 8*(block5Tau^2*(CreationSeed239.seedV block5Tau)^2) := by simpa only [mul_assoc] using hb
      _ = 8*block5Rho := by rw [block5Rho_eq]
  obtain ⟨ha,hb,hc⟩:=radical_majorants_of_rho block5Rho_nonneg block5A_positive.le
    block5C_positive.le hZ.1 hcap block5A_square block5C_square
  apply criterion_of_parameter_margin htr heq hu hZ ha hb hc
  exact half_margin_of_signs ht.le htT (block5P_positive hti) (block5Q_positive hti)
    (block5Det_positive hti)

theorem block6_criterion {t u Z:ℝ} (ht:0<t)
    (hti:t∈Icc (6119/10000:ℝ) (4993/8000:ℝ)) (heq:u=t^2*(seedV t)^2)
    (hu:u∈Icc (0:ℝ) 1) (hZ:Z∈Icc (0:ℝ) 8)
    (hcurve:u ≤ CreationSeed239.seedPhi (Z/8)) :
    (-1/((1-t^2)*(-(seedV t*seedSlope t))))*
      ((1/2:ℝ)*J/H*(1-t^2)-(44/(1-(1/2:ℝ))-32)*u-
        2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u) >
      29+2*(Real.sqrt (176*H*u)+Real.sqrt (13824*Z))/Real.sqrt (J*(1-t^2)) := by
  have htT:t ≤ seedT := hti.2.trans (by norm_num [seedT])
  have htr:t∈Icc (0:ℝ) seedT := ⟨ht.le,htT⟩
  have hcap:Z ≤ 8*block6Rho := by
    have hl:block6Left∈Icc (0:ℝ) seedT := by norm_num [block6Left,seedT]
    have hm:=parameterValue_monotone hl htr (by simpa only [block6Left] using hti.1)
    have hpar:1-block6Tau^2 ≤ u := by
      have ha:1-block6Tau^2 ≤ parameterValue block6Left := block6Tau_argument
      change parameterValue block6Left ≤ t^2*(seedV t)^2 at hm
      linarith
    have hb:=CreationSeed239.quadratic_energy_le_parameter_cap block6Tau_range hu hZ hcurve hpar
    calc
      Z ≤ 8*(block6Tau^2*(CreationSeed239.seedV block6Tau)^2) := by simpa only [mul_assoc] using hb
      _ = 8*block6Rho := by rw [block6Rho_eq]
  obtain ⟨ha,hb,hc⟩:=radical_majorants_of_rho block6Rho_nonneg block6A_positive.le
    block6C_positive.le hZ.1 hcap block6A_square block6C_square
  apply criterion_of_parameter_margin htr heq hu hZ ha hb hc
  exact half_margin_of_signs ht.le htT (block6P_positive hti) (block6Q_positive hti)
    (block6Det_positive hti)

theorem block7_criterion {t u Z:ℝ} (ht:0<t)
    (hti:t∈Icc (4993/8000:ℝ) (12727/20000:ℝ)) (heq:u=t^2*(seedV t)^2)
    (hu:u∈Icc (0:ℝ) 1) (hZ:Z∈Icc (0:ℝ) 8)
    (hcurve:u ≤ CreationSeed239.seedPhi (Z/8)) :
    (-1/((1-t^2)*(-(seedV t*seedSlope t))))*
      ((1/2:ℝ)*J/H*(1-t^2)-(44/(1-(1/2:ℝ))-32)*u-
        2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u) >
      29+2*(Real.sqrt (176*H*u)+Real.sqrt (13824*Z))/Real.sqrt (J*(1-t^2)) := by
  have htT:t ≤ seedT := hti.2.trans (by norm_num [seedT])
  have htr:t∈Icc (0:ℝ) seedT := ⟨ht.le,htT⟩
  have hcap:Z ≤ 8*block7Rho := by
    have hl:block7Left∈Icc (0:ℝ) seedT := by norm_num [block7Left,seedT]
    have hm:=parameterValue_monotone hl htr (by simpa only [block7Left] using hti.1)
    have hpar:1-block7Tau^2 ≤ u := by
      have ha:1-block7Tau^2 ≤ parameterValue block7Left := block7Tau_argument
      change parameterValue block7Left ≤ t^2*(seedV t)^2 at hm
      linarith
    have hb:=CreationSeed239.quadratic_energy_le_parameter_cap block7Tau_range hu hZ hcurve hpar
    calc
      Z ≤ 8*(block7Tau^2*(CreationSeed239.seedV block7Tau)^2) := by simpa only [mul_assoc] using hb
      _ = 8*block7Rho := by rw [block7Rho_eq]
  obtain ⟨ha,hb,hc⟩:=radical_majorants_of_rho block7Rho_nonneg block7A_positive.le
    block7C_positive.le hZ.1 hcap block7A_square block7C_square
  apply criterion_of_parameter_margin htr heq hu hZ ha hb hc
  exact half_margin_of_signs ht.le htT (block7P_positive hti) (block7Q_positive hti)
    (block7Det_positive hti)

theorem block8_criterion {t u Z:ℝ} (ht:0<t)
    (hti:t∈Icc (12727/20000:ℝ) (25943/40000:ℝ)) (heq:u=t^2*(seedV t)^2)
    (hu:u∈Icc (0:ℝ) 1) (hZ:Z∈Icc (0:ℝ) 8)
    (hcurve:u ≤ CreationSeed239.seedPhi (Z/8)) :
    (-1/((1-t^2)*(-(seedV t*seedSlope t))))*
      ((1/2:ℝ)*J/H*(1-t^2)-(44/(1-(1/2:ℝ))-32)*u-
        2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u) >
      29+2*(Real.sqrt (176*H*u)+Real.sqrt (13824*Z))/Real.sqrt (J*(1-t^2)) := by
  have htT:t ≤ seedT := hti.2.trans (by norm_num [seedT])
  have htr:t∈Icc (0:ℝ) seedT := ⟨ht.le,htT⟩
  have hcap:Z ≤ 8*block8Rho := by
    have hl:block8Left∈Icc (0:ℝ) seedT := by norm_num [block8Left,seedT]
    have hm:=parameterValue_monotone hl htr (by simpa only [block8Left] using hti.1)
    have hpar:1-block8Tau^2 ≤ u := by
      have ha:1-block8Tau^2 ≤ parameterValue block8Left := block8Tau_argument
      change parameterValue block8Left ≤ t^2*(seedV t)^2 at hm
      linarith
    have hb:=CreationSeed239.quadratic_energy_le_parameter_cap block8Tau_range hu hZ hcurve hpar
    calc
      Z ≤ 8*(block8Tau^2*(CreationSeed239.seedV block8Tau)^2) := by simpa only [mul_assoc] using hb
      _ = 8*block8Rho := by rw [block8Rho_eq]
  obtain ⟨ha,hb,hc⟩:=radical_majorants_of_rho block8Rho_nonneg block8A_positive.le
    block8C_positive.le hZ.1 hcap block8A_square block8C_square
  apply criterion_of_parameter_margin htr heq hu hZ ha hb hc
  exact half_margin_of_signs ht.le htT (block8P_positive hti) (block8Q_positive hti)
    (block8Det_positive hti)

theorem block9_criterion {t u Z:ℝ} (ht:0<t)
    (hti:t∈Icc (25943/40000:ℝ) (413/625:ℝ)) (heq:u=t^2*(seedV t)^2)
    (hu:u∈Icc (0:ℝ) 1) (hZ:Z∈Icc (0:ℝ) 8)
    (hcurve:u ≤ CreationSeed239.seedPhi (Z/8)) :
    (-1/((1-t^2)*(-(seedV t*seedSlope t))))*
      ((1/2:ℝ)*J/H*(1-t^2)-(44/(1-(1/2:ℝ))-32)*u-
        2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u) >
      29+2*(Real.sqrt (176*H*u)+Real.sqrt (13824*Z))/Real.sqrt (J*(1-t^2)) := by
  have htT:t ≤ seedT := hti.2.trans (by norm_num [seedT])
  have htr:t∈Icc (0:ℝ) seedT := ⟨ht.le,htT⟩
  have hcap:Z ≤ 8*block9Rho := by
    have hl:block9Left∈Icc (0:ℝ) seedT := by norm_num [block9Left,seedT]
    have hm:=parameterValue_monotone hl htr (by simpa only [block9Left] using hti.1)
    have hpar:1-block9Tau^2 ≤ u := by
      have ha:1-block9Tau^2 ≤ parameterValue block9Left := block9Tau_argument
      change parameterValue block9Left ≤ t^2*(seedV t)^2 at hm
      linarith
    have hb:=CreationSeed239.quadratic_energy_le_parameter_cap block9Tau_range hu hZ hcurve hpar
    calc
      Z ≤ 8*(block9Tau^2*(CreationSeed239.seedV block9Tau)^2) := by simpa only [mul_assoc] using hb
      _ = 8*block9Rho := by rw [block9Rho_eq]
  obtain ⟨ha,hb,hc⟩:=radical_majorants_of_rho block9Rho_nonneg block9A_positive.le
    block9C_positive.le hZ.1 hcap block9A_square block9C_square
  apply criterion_of_parameter_margin htr heq hu hZ ha hb hc
  exact half_margin_of_signs ht.le htT (block9P_positive hti) (block9Q_positive hti)
    (block9Det_positive hti)

theorem quartic_scalar_criterion (u:ℝ) (hu:u∈Icc (0:ℝ) 1)
    (Z:ℝ) (hZ:Z∈Icc (0:ℝ) 8) (hcurve:u ≤ CreationSeed239.seedPhi (Z/8)) :
    (-deriv seedPhi u/seedPhi u)*
      (seedAlpha u*J/H*seedPhi u-(44/(1-seedAlpha u)-32)*u-
        2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u) >
      29+2*(Real.sqrt (176*H*u)+Real.sqrt (13824*Z))/Real.sqrt (J*seedPhi u) := by
  by_cases hz:u=0
  · subst u
    simpa only [seedPhi_zero,seedAlpha,ite_true,Real.sqrt_zero,mul_zero,sub_zero,
      add_zero,zero_add,mul_one] using zero_endpoint_criterion hZ
  · have ht:=seedParameter_positive hu (lt_of_le_of_ne hu.1 (Ne.symm hz))
    have htr:=seedParameter_range hu
    have heq:=seedPhi_u_identity hu
    rw [seedQ_identity hu,seedPhi_z_identity hu]
    by_cases hcut:seedParameter u ≤ seedCut
    · simp only [seedAlpha,hz,ite_false,hcut,ite_true]
      by_cases h0:seedParameter u ≤ (563/2000:ℝ)
      · exact block0_criterion ht ⟨by exact htr.1,h0⟩ heq hu hZ hcurve
      by_cases h1:seedParameter u ≤ (1689/4000:ℝ)
      · exact block1_criterion ht ⟨by linarith,h1⟩ heq hu hZ hcurve
      by_cases h2:seedParameter u ≤ (3941/8000:ℝ)
      · exact block2_criterion ht ⟨by linarith,h2⟩ heq hu hZ hcurve
      exact block3_criterion ht ⟨by linarith,by simpa only [seedCut] using hcut⟩ heq hu hZ hcurve
    · simp only [seedAlpha,hz,ite_false,hcut]
      by_cases h4:seedParameter u ≤ (11749/20000:ℝ)
      · exact block4_criterion ht ⟨by change seedCut ≤ seedParameter u; exact (lt_of_not_ge hcut).le,h4⟩ heq hu hZ hcurve
      by_cases h5:seedParameter u ≤ (6119/10000:ℝ)
      · exact block5_criterion ht ⟨by linarith,h5⟩ heq hu hZ hcurve
      by_cases h6:seedParameter u ≤ (4993/8000:ℝ)
      · exact block6_criterion ht ⟨by linarith,h6⟩ heq hu hZ hcurve
      by_cases h7:seedParameter u ≤ (12727/20000:ℝ)
      · exact block7_criterion ht ⟨by linarith,h7⟩ heq hu hZ hcurve
      by_cases h8:seedParameter u ≤ (25943/40000:ℝ)
      · exact block8_criterion ht ⟨by linarith,h8⟩ heq hu hZ hcurve
      exact block9_criterion ht ⟨by linarith,by simpa only [seedT] using htr.2⟩ heq hu hZ hcurve

def quarticBarrier : QuarticCreationBarrier239 J where
  toScalarVariableBarrierShape := seedShape
  alpha_ge_half := fun _ hu => seedAlpha_ge_half hu
  criterion := by
    intro u hu Z hZ hcurve
    change (-deriv seedPhi u/seedPhi u)*
      (seedAlpha u*J/quarticCreationPrior239*seedPhi u-(44/(1-seedAlpha u)-32)*u-
        2*Real.sqrt (48*Z)/Real.sqrt quarticCreationPrior239*Real.sqrt u) >
      29+2*(Real.sqrt (176*quarticCreationPrior239*u)+Real.sqrt (13824*Z))/Real.sqrt (J*seedPhi u)
    have he:H=quarticCreationPrior239 := by norm_num [H,quarticCreationPrior239,CreationSeed239.B]
    rw [←he]
    exact quartic_scalar_criterion u hu Z hZ hcurve

end KLSBelow25.QuarticCreation200000
#print axioms KLSBelow25.QuarticCreation200000.quarticBarrier

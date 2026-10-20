import QuarticCreation200000Block0
import QuarticCreation200000Inverse

/-! The legal alpha patch at the zero endpoint of the actual C1 inverse.
No limiting alpha=1 is substituted into a singular denominator. -/
noncomputable section
open Set
namespace KLSBelow25.QuarticCreation200000

theorem zero_endpoint_criterion {Z : ℝ} (hZ : Z ∈ Icc (0 : ℝ) 8) :
    (-deriv seedPhi 0/seedPhi 0)*(alphaZero*J/H) >
      29+2*Real.sqrt (13824*Z)/Real.sqrt J := by
  have hv : 0 < seedV 0 := seedV_positive ⟨le_rfl,seedT_range.1.le⟩
  have hv2 : 0 < (seedV 0)^2 := sq_pos_of_pos hv
  have hder : deriv seedPhi 0 = -((seedV 0)^2)⁻¹ := by
    rw [(hasDerivAt_seedPhi (by norm_num : (0 : ℝ) ∈ Icc 0 1)).deriv]
    simp [seedParameter,seedPhi_zero,RadicalBarrier.parameter,seedSlope,pow_two]
  have hJroot : 0 < Real.sqrt J := Real.sqrt_pos.mpr J_positive
  have hJroot2 := Real.sq_sqrt J_positive.le
  have hZroot := Real.sq_sqrt (by linarith [hZ.1] : (0 : ℝ) ≤ 13824*Z)
  have hc2 : 4*110592/J ≤ block0C^2 := by
    simpa only [block0Rho_eq,mul_one] using block0C_square
  have hcJ : 4*110592 ≤ block0C^2*J := (div_le_iff₀ J_positive).mp hc2
  have hrootcap : 2*Real.sqrt (13824*Z) ≤ block0C*Real.sqrt J := by
    have he : (block0C*Real.sqrt J)^2 = block0C^2*J := by
      rw [mul_pow,hJroot2]
    have hsq : (2*Real.sqrt (13824*Z))^2 ≤ (block0C*Real.sqrt J)^2 := by
      rw [he]
      nlinarith [hZ.2]
    exact (sq_le_sq₀ (by positivity)
      (mul_nonneg block0C_positive.le hJroot.le)).mp hsq
  have hcap : 2*Real.sqrt (13824*Z)/Real.sqrt J ≤ block0C :=
    (div_le_iff₀ hJroot).mpr hrootcap
  have hstrict : 29+block0C < ((seedV 0)^2)⁻¹*(alphaZero*J/H) := by
    have hm := zero_strict_margin
    have hd : 29+block0C < (alphaZero*J/H)/(seedV 0)^2 :=
      (lt_div_iff₀ hv2).mpr (by convert hm using 1 <;> ring)
    simpa only [div_eq_mul_inv,mul_comm] using hd
  rw [seedPhi_zero,hder]
  simp only [neg_neg,div_one]
  exact lt_of_le_of_lt (by linarith :
    29+2*Real.sqrt (13824*Z)/Real.sqrt J ≤ 29+block0C) hstrict

end KLSBelow25.QuarticCreation200000

#print axioms KLSBelow25.QuarticCreation200000.zero_endpoint_criterion

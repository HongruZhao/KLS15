import KLSConstantImprovement.DeficitCurvatureScalar

/-! Scalar consequences of the exact critical covariance/signed-trace block.
The original-law classification, operator block split, and complement-mass
bound remain explicit inputs. A positive fixed-law spectral gap is not
asserted uniformly over laws or dimensions. -/
noncomputable section
namespace KLSConstantImprovement.CriticalKernelSectorScalar

theorem complement_additive_budget {N N0 N1 V S L : ℝ}
    (hN : N = N0+N1) (hV : V ≤ 216*N0+L*N1)
    (hS : 4*N0-8*N1 ≤ S) :
    92*N-(L+36)*N1 ≤ 224*N+21*S-V := by
  nlinarith

theorem critical_mass_variance_bound {N N0 N1 V L : ℝ}
    (hN : N = N0+N1) (hL : 216 ≤ L)
    (hmass : N1 ≤ N/16) (hV : V ≤ 216*N0+L*N1) :
    V ≤ (216+(L-216)/16)*N := by
  have hp := mul_le_mul_of_nonneg_left hmass (sub_nonneg.mpr hL)
  nlinarith

theorem critical_mass_signed_bound {N N0 N1 S : ℝ}
    (hN : N = N0+N1) (hmass : N1 ≤ N/16)
    (hS : 4*N0-8*N1 ≤ S) :
    (13/4:ℝ)*N ≤ S := by
  linarith

theorem retained_raw_critical_sector {N N0 N1 V S : ℝ}
    (hN0 : 0 < N) (hN : N = N0+N1) (hmass : N1 ≤ N/16)
    (hV : V ≤ 216*N0+(4302/5:ℝ)*N1)
    (hS : 4*N0-8*N1 ≤ S) :
    V ≤ (10251/40:ℝ)*N ∧ (13/4:ℝ)*N ≤ S ∧
      (1439/40:ℝ)*N ≤ 224*N+21*S-V ∧ V < 308*N := by
  have hv := critical_mass_variance_bound hN (by norm_num : (216:ℝ) ≤ 4302/5) hmass hV
  have hs := critical_mass_signed_bound hN hmass hS
  refine ⟨by nlinarith,hs,by nlinarith,by nlinarith⟩

theorem joint_raw_critical_sector {N N0 N1 V S : ℝ}
    (hN0 : 0 < N) (hN : N = N0+N1) (hmass : N1 ≤ N/16)
    (hV : V ≤ 216*N0+(107334/125:ℝ)*N1)
    (hS : 4*N0-8*N1 ≤ S) :
    V ≤ (256167/1000:ℝ)*N ∧ (13/4:ℝ)*N ≤ S ∧
      (36083/1000:ℝ)*N ≤ 224*N+21*S-V ∧ V < 308*N := by
  have hv := critical_mass_variance_bound hN (by norm_num : (216:ℝ) ≤ 107334/125) hmass hV
  have hs := critical_mass_signed_bound hN hmass hS
  refine ⟨by nlinarith,hs,by nlinarith,by nlinarith⟩

theorem fixed_law_gap_implies_complement_mass {N N1 d lambda : ℝ}
    (hlambda : 0 < lambda) (hlower : lambda*N1 ≤ d)
    (hsmall : d ≤ lambda*N/16) : N1 ≤ N/16 := by
  apply (mul_le_mul_iff_of_pos_left hlambda).mp
  nlinarith

end KLSConstantImprovement.CriticalKernelSectorScalar
#print axioms KLSConstantImprovement.CriticalKernelSectorScalar.complement_additive_budget
#print axioms KLSConstantImprovement.CriticalKernelSectorScalar.critical_mass_variance_bound
#print axioms KLSConstantImprovement.CriticalKernelSectorScalar.critical_mass_signed_bound
#print axioms KLSConstantImprovement.CriticalKernelSectorScalar.retained_raw_critical_sector
#print axioms KLSConstantImprovement.CriticalKernelSectorScalar.joint_raw_critical_sector
#print axioms KLSConstantImprovement.CriticalKernelSectorScalar.fixed_law_gap_implies_complement_mass

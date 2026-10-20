import SingleSlotCounterexampleWhitening
import UniversalTwoSlot

/-! An exact strict violation of cap four for the original actual
third-cumulant matrix. The law is constructed and whitened in the imported
modules; its log-concavity is joined to this result in the final module. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ENNReal
namespace KLSImprovement.SingleSlotCounterexample
open KLS KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def gamma :ℝ := (53909/13500:ℝ)/Real.sqrt vS^3
def beta :ℝ := (293/134175:ℝ)/(vS*Real.sqrt vW)
def delta :ℝ := (51270294/80013025:ℝ)/(Real.sqrt vS*vW)

theorem isotropic_third000 :(∫x:Space 2,x 0^3 ∂isotropicMeasure)=gamma := by
  have h:=integral_isotropic_monomial 3 0
  simp only [pow_zero,mul_one] at h
  rw [raw_s_third] at h
  exact h
theorem isotropic_third001 :(∫x:Space 2,x 0^2*x 1 ∂isotropicMeasure)=beta := by
  have h:=integral_isotropic_monomial 2 1
  simp only [pow_one] at h
  rw [raw_ssw_third,Real.sq_sqrt (by norm_num : (0:ℝ)≤vS)] at h
  exact h
theorem isotropic_third011 :(∫x:Space 2,x 0*x 1^2 ∂isotropicMeasure)=delta := by
  have h:=integral_isotropic_monomial 1 2
  simp only [pow_one] at h
  rw [raw_sww_third,Real.sq_sqrt (by norm_num : (0:ℝ)≤vW)] at h
  exact h

def kappa (k:Fin 2):Matrix (Fin 2) (Fin 2) ℝ :=
  thirdCumulantMatrix isotropicMeasure (MomentMap.coordinateVector k)
def singleSlotGram :Matrix (Fin 2) (Fin 2) ℝ := ∑k:Fin 2,kappa k*kappa k

theorem kappa_symm (k i j:Fin 2):kappa k i j=kappa k j i := by
  unfold kappa
  rw [thirdCumulantMatrix_coordinate_eq_cubic,thirdCumulantMatrix_coordinate_eq_cubic]
  apply integral_congr_ae
  exact .of_forall (fun x=>by ring)

theorem kappa_entry_zero (k j:Fin 2):kappa k 0 j=
    if k=0 then (if j=0 then gamma else beta) else (if j=0 then beta else delta) := by
  fin_cases k <;>fin_cases j
  · change kappa 0 0 0=gamma
    rw [kappa,thirdCumulantMatrix_coordinate_eq_cubic]
    calc
      _ = ∫x:Space 2,x 0^3 ∂isotropicMeasure := by
        apply integral_congr_ae
        exact .of_forall (fun x=>by ring)
      _ = gamma := isotropic_third000
  · change kappa 0 0 1=beta
    rw [kappa,thirdCumulantMatrix_coordinate_eq_cubic]
    calc
      _ = ∫x:Space 2,x 0^2*x 1 ∂isotropicMeasure := by
        apply integral_congr_ae
        exact .of_forall (fun x=>by ring)
      _ = beta := isotropic_third001
  · change kappa 1 0 0=beta
    rw [kappa,thirdCumulantMatrix_coordinate_eq_cubic]
    calc
      _ = ∫x:Space 2,x 0^2*x 1 ∂isotropicMeasure := by
        apply integral_congr_ae
        exact .of_forall (fun x=>by ring)
      _ = beta := isotropic_third001
  · change kappa 1 0 1=delta
    rw [kappa,thirdCumulantMatrix_coordinate_eq_cubic]
    calc
      _ = ∫x:Space 2,x 0*x 1^2 ∂isotropicMeasure := by
        apply integral_congr_ae
        exact .of_forall (fun x=>by ring)
      _ = delta := isotropic_third011

theorem singleSlotGram_zero_zero :singleSlotGram 0 0=gamma^2+2*beta^2+delta^2 := by
  simp only [singleSlotGram,Matrix.sum_apply,Matrix.mul_apply,Fin.sum_univ_two]
  rw [kappa_symm 0 1 0,kappa_symm 1 1 0]
  norm_num only [kappa_entry_zero,ite_true,ite_false,show (1:Fin 2)≠0 by decide]
  ring

theorem gamma_sq :gamma^2=(53909/13500:ℝ)^2/vS^3 := by
  unfold gamma
  rw [div_pow]
  have h:(Real.sqrt vS^3)^2=vS^3 := by
    calc
      _ = (Real.sqrt vS^2)^3 := by ring
      _ = vS^3 := by rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤vS)]
  rw [h]
theorem beta_sq :beta^2=(293/134175:ℝ)^2/(vS^2*vW) := by
  unfold beta
  rw [div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤vW)]
theorem delta_sq :delta^2=(51270294/80013025:ℝ)^2/(vS*vW^2) := by
  unfold delta
  rw [div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤vS)]

theorem singleSlotGram_exact :singleSlotGram 0 0=
    (1500003162676/374737767181:ℝ) := by
  rw [singleSlotGram_zero_zero,gamma_sq,beta_sq,delta_sq]
  norm_num [vS,vW]

theorem singleSlotGram_exceeds_four :4<singleSlotGram 0 0 := by
  rw [singleSlotGram_exact]
  norm_num

theorem isotropicMeasure_not_cap_four :
    ¬((4:ℝ) • (1:Matrix (Fin 2) (Fin 2) ℝ)-singleSlotGram).PosSemidef := by
  intro h
  have hd:0≤((4:ℝ) • (1:Matrix (Fin 2) (Fin 2) ℝ)-singleSlotGram) 0 0 := h.diag_nonneg
  simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply,ite_true,
    smul_eq_mul,mul_one] at hd
  linarith [singleSlotGram_exceeds_four]

end KLSImprovement.SingleSlotCounterexample
#print axioms KLSImprovement.SingleSlotCounterexample.singleSlotGram_exact
#print axioms KLSImprovement.SingleSlotCounterexample.isotropicMeasure_not_cap_four

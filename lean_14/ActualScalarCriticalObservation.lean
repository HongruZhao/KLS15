import ScalarExponentialAppellBridge
import ExponentialCriticalGram
import ActualAppellJointContinuity

/-! The K=4 weighted bound for the actual centered scalar exponential,
through the original all-order normalized tilt/Appell energy definition. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace KLSImprovement.ActualScalarCritical
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSImprovement.ProductAdmissible KLSImprovement.ActualProductCumulants
open KLSImprovement.ScalarExponentialBridge KLSImprovement.ExponentialCriticalGram
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

def scalarCenter (y : ℝ) : Space 1 := centerAffine 1 (scalarEmbed y)
def pullback (f : Space 1 → ℝ) (y : ℝ) : ℝ := f (scalarCenter y)

theorem centered_integral (g : Space 1 → ℝ) :
    (∫ x,g x ∂centeredProductMeasure 1)=∫ y,g (scalarCenter y) ∂expMeasure 1 := by
  rw [centeredProduct_eq_raw_map,raw_eq_scalar_map]
  change (∫ x,g x ∂((expMeasure 1).map scalarEmbed).map (centerAffine 1).toHomeomorph)=_
  rw [(centerAffine 1).toHomeomorph.isClosedEmbedding.integral_map]
  change (∫ x,g (centerAffine 1 x) ∂(expMeasure 1).map scalarEmbed.toHomeomorph)=_
  rw [scalarEmbed.toHomeomorph.isClosedEmbedding.integral_map]
  rfl

theorem pullback_memLp {f : Space 1 → ℝ}
    (hf : MemLp f 2 (centeredProductMeasure 1)) :
    MemLp (pullback f) 2 (expMeasure 1) := by
  rw [centeredProduct_eq_raw_map] at hf
  have hraw := hf.comp_of_map (centerAffine 1).continuous.measurable.aemeasurable
  rw [raw_eq_scalar_map] at hraw
  exact hraw.comp_of_map scalarEmbed.continuous.measurable.aemeasurable

theorem original_coefficient_eq_scalar_integral {f : Space 1 → ℝ}
    (hf : MemLp f 2 (centeredProductMeasure 1)) (m : ℕ) :
    actualAppellCoefficient (centeredProductMeasure 1) f (m+1) (fun _ => 0)=
      ∫ y,pullback f y*KLSImprovement.Exponential.appell m y ∂expMeasure 1 := by
  rw [centered_actual_Appell_coefficient hf,centered_integral]
  apply integral_congr_ae
  exact .of_forall (fun y => by
    have he : scalarCenter y 0+1=y := by
      change (-1:ℝ)+y+1=y
      ring
    change f (scalarCenter y)*KLSImprovement.Exponential.appell m (scalarCenter y 0+1)=_
    rw [he]
    rfl)

theorem original_weighted_coefficient {f : Space 1 → ℝ}
    (hf : MemLp f 2 (centeredProductMeasure 1)) (m : ℕ) :
    actualAppellCoefficient (centeredProductMeasure 1) f (m+1) (fun _ => 0)/
      ((2:ℝ)^(m+1)*((m+1).factorial:ℝ))=
      ∫ y,pullback f y*weightedAppell m y ∂expMeasure 1 := by
  rw [original_coefficient_eq_scalar_integral hf]
  unfold weightedAppell
  simp_rw [←mul_div_assoc]
  rw [integral_div]

theorem original_energy_one (f : Space 1 → ℝ) (m : ℕ) :
    actualAppellEnergy (centeredProductMeasure 1) f m=
      (actualAppellCoefficient (centeredProductMeasure 1) f m (fun _ => 0))^2 := by
  simp only [actualAppellEnergy,Fintype.sum_unique]
  rfl

theorem original_weighted_energy_eq {f : Space 1 → ℝ}
    (hf : MemLp f 2 (centeredProductMeasure 1)) (m : ℕ) :
    actualAppellEnergy (centeredProductMeasure 1) f (m+1)/
      ((4:ℝ)^(m+1)*((m+1).factorial:ℝ)^2)=
      (∫ y,pullback f y*weightedAppell m y ∂expMeasure 1)^2 := by
  rw [←original_weighted_coefficient hf,original_energy_one,div_pow,mul_pow]
  congr 2
  rw [←pow_mul,show (m+1)*2=2*(m+1) by omega,pow_mul]
  norm_num

theorem actual_scalar_critical_finite_budget (M : ℕ) {f : Space 1 → ℝ}
    (hf : MemLp f 2 (centeredProductMeasure 1)) :
    (∑ m : Fin M, actualAppellEnergy (centeredProductMeasure 1) f (m.val+1)/
      ((4:ℝ)^(m.val+1)*((m.val+1).factorial:ℝ)^2))≤
      (1/2:ℝ)*(∫ x,(f x)^2 ∂centeredProductMeasure 1) := by
  simp_rw [original_weighted_energy_eq hf]
  rw [centered_integral]
  exact exponential_weighted_Appell_finite_budget M (pullback_memLp hf)

theorem actual_scalar_critical_summable {f : Space 1 → ℝ}
    (hf : MemLp f 2 (centeredProductMeasure 1)) :
    Summable (fun m : ℕ => actualAppellEnergy (centeredProductMeasure 1) f (m+1)/
      ((4:ℝ)^(m+1)*((m+1).factorial:ℝ)^2)) := by
  apply summable_of_sum_range_le
    (fun m => div_nonneg (actualAppellEnergy_nonneg _ _ _) (by positivity))
  intro M
  rw [←Fin.sum_univ_eq_sum_range
    (fun m : ℕ => actualAppellEnergy (centeredProductMeasure 1) f (m+1)/
      ((4:ℝ)^(m+1)*((m+1).factorial:ℝ)^2)) M]
  exact actual_scalar_critical_finite_budget M hf

theorem actual_scalar_critical_budget {f : Space 1 → ℝ}
    (hf : MemLp f 2 (centeredProductMeasure 1)) :
    (∑' m : ℕ,actualAppellEnergy (centeredProductMeasure 1) f (m+1)/
      ((4:ℝ)^(m+1)*((m+1).factorial:ℝ)^2))≤
      (1/2:ℝ)*(∫ x,(f x)^2 ∂centeredProductMeasure 1) := by
  apply Real.tsum_le_of_sum_range_le
    (fun m => div_nonneg (actualAppellEnergy_nonneg _ _ _) (by positivity))
  intro M
  rw [←Fin.sum_univ_eq_sum_range
    (fun m : ℕ => actualAppellEnergy (centeredProductMeasure 1) f (m+1)/
      ((4:ℝ)^(m+1)*((m+1).factorial:ℝ)^2)) M]
  exact actual_scalar_critical_finite_budget M hf

theorem actual_scalar_critical_tail_summable {f : Space 1 → ℝ}
    (hf : MemLp f 2 (centeredProductMeasure 1)) :
    Summable (fun m : ℕ => actualAppellEnergy (centeredProductMeasure 1) f (m+2)/
      ((4:ℝ)^(m+2)*((m+2).factorial:ℝ)^2)) := by
  simpa only [Nat.add_assoc] using
    (summable_nat_add_iff 1).2 (actual_scalar_critical_summable hf)

theorem actual_scalar_critical_charged_budget {f : Space 1 → ℝ}
    (hf : MemLp f 2 (centeredProductMeasure 1)) :
    (∑' m : ℕ,actualAppellEnergy (centeredProductMeasure 1) f (m+2)/
      ((4:ℝ)^(m+2)*((m+2).factorial:ℝ)^2))+
      (∫ x : Space 1,f x*x 0 ∂centeredProductMeasure 1)^2/4≤
      (1/2:ℝ)*(∫ x,(f x)^2 ∂centeredProductMeasure 1) := by
  have h := actual_scalar_critical_budget hf
  rw [(actual_scalar_critical_summable hf).tsum_eq_zero_add] at h
  have he : actualAppellEnergy (centeredProductMeasure 1) f 1=
      (∫ x : Space 1,f x*x 0 ∂centeredProductMeasure 1)^2 := by
    rw [original_energy_one,centered_actual_Appell_coefficient hf 0]
    simp [KLSImprovement.Exponential.appell]
  simp only [Nat.zero_add,Nat.factorial_one,Nat.cast_one,pow_one,one_pow,
    mul_one,Nat.add_assoc,Nat.reduceAdd,he] at h
  linarith

theorem actual_scalar_critical_degrees_ge_two_budget {f : Space 1 → ℝ}
    (hf : MemLp f 2 (centeredProductMeasure 1)) :
    (∑' m : ℕ,actualAppellEnergy (centeredProductMeasure 1) f (m+2)/
      ((4:ℝ)^(m+2)*((m+2).factorial:ℝ)^2))≤
      (1/2:ℝ)*(∫ x,(f x)^2 ∂centeredProductMeasure 1) := by
  have h := actual_scalar_critical_charged_budget hf
  have hn : 0≤(∫ x : Space 1,f x*x 0 ∂centeredProductMeasure 1)^2/4 := by positivity
  linarith

end KLSImprovement.ActualScalarCritical
#print axioms KLSImprovement.ActualScalarCritical.original_coefficient_eq_scalar_integral
#print axioms KLSImprovement.ActualScalarCritical.actual_scalar_critical_finite_budget
#print axioms KLSImprovement.ActualScalarCritical.actual_scalar_critical_summable
#print axioms KLSImprovement.ActualScalarCritical.actual_scalar_critical_budget
#print axioms KLSImprovement.ActualScalarCritical.actual_scalar_critical_tail_summable
#print axioms KLSImprovement.ActualScalarCritical.actual_scalar_critical_charged_budget
#print axioms KLSImprovement.ActualScalarCritical.actual_scalar_critical_degrees_ge_two_budget

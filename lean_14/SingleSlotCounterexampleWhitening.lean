import SingleSlotCounterexampleMoments
import KLS.AffineWhitening

/-! Explicit covariance whitening of the actual two-cone law. The two
coordinates are the standardized sum and its orthogonal residual. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ENNReal
namespace KLSImprovement.SingleSlotCounterexample
open KLS
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
local instance :IsProbabilityMeasure rawMeasure := raw_isProbability

abbrev vS :ℝ := 1789/900
abbrev vW :ℝ := 14473/44725
abbrev regression :ℝ := 5364/8945

def whiteningMatrix :Matrix (Fin 2) (Fin 2) ℝ :=
  !![1/Real.sqrt vS,1/Real.sqrt vS;
     -regression/Real.sqrt vW,(1-regression)/Real.sqrt vW]
def whiteningTranslation :Space 2 := WithLp.toLp 2
  ![-(59/30:ℝ)/Real.sqrt vS,(-(29/25:ℝ)+regression*(59/30:ℝ))/Real.sqrt vW]
def whiteningMap :Space 2→ᴬ[ℝ]Space 2 :=
  affineMatrixMap whiteningMatrix whiteningTranslation
def isotropicMeasure :Measure (Space 2) := rawMeasure.map whiteningMap

theorem whiteningMap_apply (x:Space 2):whiteningMap x=
    WithLp.toLp 2 ![polyEval sPoly x/Real.sqrt vS,polyEval wPoly x/Real.sqrt vW] := by
  ext i
  fin_cases i <;>simp [whiteningMap,affineMatrixMap_apply,PiLp.add_apply,
    matrixAction_apply,whiteningMatrix,whiteningTranslation,PiLp.toLp_apply,
    Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    polyEval,sPoly,wPoly,MvPolynomial.eval_sub,MvPolynomial.eval_add,
    MvPolynomial.eval_mul,MvPolynomial.eval_C,MvPolynomial.eval_X] <;>ring

theorem whiteningMap_zero (x:Space 2):(whiteningMap x) 0=polyEval sPoly x/Real.sqrt vS := by
  rw [whiteningMap_apply]
  rfl
theorem whiteningMap_one (x:Space 2):(whiteningMap x) 1=polyEval wPoly x/Real.sqrt vW := by
  rw [whiteningMap_apply]
  rfl

theorem integral_whiteningMap_monomial (p q:ℕ):
    (∫x,(whiteningMap x) 0^p*(whiteningMap x) 1^q ∂rawMeasure)=
      rawMoment (sPoly^p*wPoly^q)/(Real.sqrt vS^p*Real.sqrt vW^q) := by
  have he:(fun x:Space 2=>(whiteningMap x) 0^p*(whiteningMap x) 1^q)=
      (fun x=>polyEval (sPoly^p*wPoly^q) x/(Real.sqrt vS^p*Real.sqrt vW^q)) := by
    funext x
    rw [whiteningMap_zero,whiteningMap_one]
    simp only [polyEval,MvPolynomial.eval_mul,MvPolynomial.eval_pow,
      div_pow,mul_div_mul_comm]
  rw [he]
  simp only [div_eq_mul_inv,integral_mul_const]
  rfl

theorem integral_isotropic_monomial (p q:ℕ):
    (∫x:Space 2,x 0^p*x 1^q ∂isotropicMeasure)=
      rawMoment (sPoly^p*wPoly^q)/(Real.sqrt vS^p*Real.sqrt vW^q) := by
  rw [isotropicMeasure,integral_map whiteningMap.continuous.measurable.aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun x:Space 2=>x 0^p*x 1^q) _)]
  exact integral_whiteningMap_monomial p q

theorem whiteningMap_coordinate_memLp (i:Fin 2):
    MemLp (fun x=>(whiteningMap x) i) 2 rawMeasure := by
  fin_cases i
  · change MemLp (fun x=>(whiteningMap x) 0) 2 rawMeasure
    have he:(fun x:Space 2=>(whiteningMap x) 0)=
        (fun x=>(Real.sqrt vS)⁻¹*polyEval sPoly x) := by
      funext x
      rw [whiteningMap_zero]
      ring
    rw [he]
    exact (memLp_raw_polynomial sPoly).const_mul _
  · change MemLp (fun x=>(whiteningMap x) 1) 2 rawMeasure
    have he:(fun x:Space 2=>(whiteningMap x) 1)=
        (fun x=>(Real.sqrt vW)⁻¹*polyEval wPoly x) := by
      funext x
      rw [whiteningMap_one]
      ring
    rw [he]
    exact (memLp_raw_polynomial wPoly).const_mul _

theorem whiteningMap_zero_mean :(∫x,(whiteningMap x) 0 ∂rawMeasure)=0 := by
  have h:=integral_whiteningMap_monomial 1 0
  simp only [pow_one,pow_zero,mul_one] at h
  rw [raw_s_mean,zero_div] at h
  exact h
theorem whiteningMap_one_mean :(∫x,(whiteningMap x) 1 ∂rawMeasure)=0 := by
  have h:=integral_whiteningMap_monomial 0 1
  simp only [pow_one,pow_zero,one_mul] at h
  rw [raw_w_mean,zero_div] at h
  exact h

theorem whiteningMap_zero_second :
    (∫x,(whiteningMap x) 0*(whiteningMap x) 0 ∂rawMeasure)=1 := by
  have h:=integral_whiteningMap_monomial 2 0
  simp only [pow_zero,mul_one] at h
  rw [raw_s_second,Real.sq_sqrt (by norm_num : (0:ℝ)≤vS)] at h
  norm_num only [vS,div_self (by norm_num : (1789/900:ℝ)≠0)] at h
  simpa only [pow_two] using h
theorem whiteningMap_one_second :
    (∫x,(whiteningMap x) 1*(whiteningMap x) 1 ∂rawMeasure)=1 := by
  have h:=integral_whiteningMap_monomial 0 2
  simp only [pow_zero,one_mul] at h
  rw [raw_w_second,Real.sq_sqrt (by norm_num : (0:ℝ)≤vW)] at h
  norm_num only [vW,div_self (by norm_num : (14473/44725:ℝ)≠0)] at h
  simpa only [pow_two] using h
theorem whiteningMap_cross_second :
    (∫x,(whiteningMap x) 0*(whiteningMap x) 1 ∂rawMeasure)=0 := by
  have h:=integral_whiteningMap_monomial 1 1
  simp only [pow_one] at h
  rw [raw_sw_second,zero_div] at h
  exact h

theorem isotropicMeasure_isProbability :IsProbabilityMeasure isotropicMeasure :=
  (Measure.isProbabilityMeasure_map_iff whiteningMap.continuous.measurable.aemeasurable).mpr
    inferInstance

theorem isotropicMeasure_isIsotropic :IsIsotropic isotropicMeasure := by
  apply isIsotropic_map_of_coordinateMoments whiteningMap.continuous.measurable
    whiteningMap_coordinate_memLp
  · intro i
    fin_cases i
    · exact whiteningMap_zero_mean
    · exact whiteningMap_one_mean
  · intro i j
    fin_cases i <;>fin_cases j
    · exact whiteningMap_zero_second
    · exact whiteningMap_cross_second
    · change (∫x,(whiteningMap x) 1*(whiteningMap x) 0 ∂rawMeasure)=0
      calc
        _ = ∫x,(whiteningMap x) 0*(whiteningMap x) 1 ∂rawMeasure := by
          apply integral_congr_ae
          exact .of_forall (fun x=>mul_comm _ _)
        _ = 0 := whiteningMap_cross_second
    · exact whiteningMap_one_second

end KLSImprovement.SingleSlotCounterexample
#print axioms KLSImprovement.SingleSlotCounterexample.isotropicMeasure_isIsotropic
#print axioms KLSImprovement.SingleSlotCounterexample.integral_isotropic_monomial

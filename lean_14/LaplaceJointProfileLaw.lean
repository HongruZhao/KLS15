import TwoConeCubicFamily
import ScalarExponentialAppellBridge
import KLS.SuspensionIsotropy

/-! The actual variance-one symmetric Laplace law, obtained as an affine
image of the proved two-cone law at d=1,g=0. No moment input is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory MvPolynomial
open scoped BigOperators ENNReal
namespace KLSImprovement.LaplaceJoint
open KLS KLSImprovement.TwoConeMoments
open KLSImprovement.SingleSlotCounterexample (Poly polyEval polyEval_measurable)
open KLSImprovement.ScalarExponentialBridge (scalarEmbed scalarEmbed_apply)
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def baseMeasure : Measure (Space 2) := rawMeasure 1 0
local instance : IsProbabilityMeasure baseMeasure := raw_isProbability (by norm_num) 0

def laplaceLinear : Space 2→L[ℝ]Space 1 :=
  (1/Real.sqrt 2:ℝ) • scalarEmbed.toContinuousLinearMap.comp
    (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2))
def laplaceProjection : Space 2→ᴬ[ℝ]Space 1 := laplaceLinear.toContinuousAffineMap
def laplaceMeasure : Measure (Space 1) := baseMeasure.map laplaceProjection

@[simp] theorem laplaceProjection_apply (x : Space 2) (i : Fin 1) :
    laplaceProjection x i=x 1/Real.sqrt 2 := by
  change (1/Real.sqrt 2:ℝ)*x 1=x 1/Real.sqrt 2
  ring

theorem laplaceMeasure_isProbability : IsProbabilityMeasure laplaceMeasure :=
  (Measure.isProbabilityMeasure_map_iff laplaceProjection.continuous.measurable.aemeasurable).mpr
    inferInstance
local instance : IsProbabilityMeasure laplaceMeasure := laplaceMeasure_isProbability

theorem laplaceMeasure_logConcave : measureLogConcave laplaceMeasure := by
  have : IsProbabilityMeasure (rawMeasure 1 0) := raw_isProbability (by norm_num) 0
  exact (KLSImprovement.TwoConeLogConcave.raw_logConcave
    (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)≤0)
    (by norm_num : (0:ℝ)≤1)).map_continuousAffineMap laplaceProjection

theorem memLp_base_polynomial (p : Poly) : MemLp (polyEval p) 2 baseMeasure := by
  apply (memLp_two_iff_integrable_sq (polyEval_measurable p).aestronglyMeasurable).mpr
  apply (integrable_raw_polynomial 1 0 (p*p)).congr
  exact .of_forall (fun x=>by simp only [polyEval,MvPolynomial.eval_mul,pow_two])

theorem projection_power_memLp (m : ℕ) :
    MemLp (fun x:Space 2=>(laplaceProjection x) 0^m) 2 baseMeasure := by
  have he : (fun x:Space 2=>(laplaceProjection x) 0^m)=
      (fun x=>polyEval (X (1:Fin 2)^m) x/(Real.sqrt 2)^m) := by
    funext x
    simp only [laplaceProjection_apply,div_pow,polyEval,MvPolynomial.eval_pow,MvPolynomial.eval_X]
  rw [he]
  simpa only [div_eq_mul_inv] using
    (memLp_base_polynomial (X (1:Fin 2)^m)).mul_const ((Real.sqrt 2)^m)⁻¹

theorem integral_projection_power (m : ℕ) :
    (∫ x:Space 2,(laplaceProjection x) 0^m ∂baseMeasure)=
      ((m.factorial:ℝ)*(1+(-1:ℝ)^m)/2)/(Real.sqrt 2)^m := by
  have he : (fun x:Space 2=>(laplaceProjection x) 0^m)=
      (fun x=>polyEval (X (1:Fin 2)^m) x/(Real.sqrt 2)^m) := by
    funext x
    simp only [laplaceProjection_apply,div_pow,polyEval,MvPolynomial.eval_pow,MvPolynomial.eval_X]
  rw [he,integral_div]
  change rawMoment 1 0 (X (1:Fin 2)^m)/(Real.sqrt 2)^m=_
  rw [rawMoment_eq_qMoment (by norm_num)]
  have h := qMoment_monomial 1 0 0 m
  norm_num only [pow_zero,one_mul,Nat.factorial_zero,Nat.cast_one,Finset.range_one,
    Finset.sum_singleton,Nat.choose_zero_right,Nat.sub_zero,zero_add,zero_sub,
    Nat.zero_sub,zero_mul,add_zero,one_pow] at h
  rw [h]
  norm_num
  ring

theorem laplaceMeasure_isIsotropic : IsIsotropic laplaceMeasure := by
  apply isIsotropic_map_of_coordinateMoments laplaceProjection.continuous.measurable
  · intro i
    have hi:i=(0:Fin 1) := Subsingleton.elim _ _
    subst i
    simpa only [pow_one] using projection_power_memLp 1
  · intro i
    have hi:i=(0:Fin 1) := Subsingleton.elim _ _
    subst i
    have h:=integral_projection_power 1
    norm_num at h
    simpa only [laplaceProjection_apply] using h
  · intro i j
    have hi:i=(0:Fin 1) := Subsingleton.elim _ _
    have hj:j=(0:Fin 1) := Subsingleton.elim _ _
    subst i
    subst j
    have h:=integral_projection_power 2
    rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)] at h
    norm_num at h
    simpa only [pow_two,ite_true,laplaceProjection_apply] using h

theorem laplaceMeasure_admissible : admissibleMeasure laplaceMeasure :=
  ⟨laplaceMeasure_isProbability,laplaceMeasure_logConcave,laplaceMeasure_isIsotropic⟩

theorem laplace_power_memLp (m : ℕ) :
    MemLp (fun x:Space 1=>x 0^m) 2 laplaceMeasure :=
  (memLp_map_measure_iff (by fun_prop)
    laplaceProjection.continuous.measurable.aemeasurable).mpr (projection_power_memLp m)

theorem laplace_power_integrable (m : ℕ) :
    Integrable (fun x:Space 1=>x 0^m) laplaceMeasure :=
  (laplace_power_memLp m).integrable (by norm_num : (1:ℝ≥0∞)≤2)

theorem integral_laplace_power (m : ℕ) :
    (∫ x:Space 1,x 0^m ∂laplaceMeasure)=
      ((m.factorial:ℝ)*(1+(-1:ℝ)^m)/2)/(Real.sqrt 2)^m := by
  rw [laplaceMeasure,integral_map laplaceProjection.continuous.measurable.aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun x:Space 1=>x 0^m) _)]
  exact integral_projection_power m

theorem integral_laplace_even (m : ℕ) :
    (∫ x:Space 1,x 0^(2*m) ∂laplaceMeasure)=((2*m).factorial:ℝ)/(2:ℝ)^m := by
  rw [integral_laplace_power]
  simp only [pow_mul,neg_one_sq,one_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  ring

theorem integral_laplace_odd (m : ℕ) :
    (∫ x:Space 1,x 0^(2*m+1) ∂laplaceMeasure)=0 := by
  rw [integral_laplace_power]
  simp [pow_add,pow_mul]

end KLSImprovement.LaplaceJoint
#print axioms KLSImprovement.LaplaceJoint.laplaceMeasure_admissible
#print axioms KLSImprovement.LaplaceJoint.laplace_power_memLp
#print axioms KLSImprovement.LaplaceJoint.integral_laplace_even
#print axioms KLSImprovement.LaplaceJoint.integral_laplace_odd

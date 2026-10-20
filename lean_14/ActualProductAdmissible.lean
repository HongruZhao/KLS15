import ProductExponentialPolynomialMoments
import ActualProductCumulants
import KLS.GaussianExample
import KLS.SuspensionIsotropy
import KLS.DensityToClass
import KLS.LogConcavityAffine

/-! The concrete centered independent exponential law belongs to the original
admissible class. No Appell or Poincaré bound is used to establish this fact. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators ENNReal
namespace KLSImprovement.ProductAdmissible
open KLS KLSImprovement.ProductPolynomial KLSImprovement.ExponentialMoments
open KLSImprovement.ActualProductCumulants
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

theorem centeredProduct_isProbability (n:ℕ) : IsProbabilityMeasure (centeredProductMeasure n) := by
  unfold centeredProductMeasure
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_centeredProductMap n).aemeasurable).mpr inferInstance

theorem centeredProduct_isIsotropic (n:ℕ) : IsIsotropic (centeredProductMeasure n) := by
  apply isIsotropic_map_of_coordinateMoments (measurable_centeredProductMap n)
  · intro i
    exact memLp_copy expMeasure_one_memLp_centered i
  · intro i
    change (∫ y:Fin n→ℝ,y i-1 ∂product n)=0
    rw [product,integral_comp_eval (μ:=fun _:Fin n=>expMeasure 1) (i:=i)
      (f:=fun y:ℝ=>y-1) (by fun_prop)]
    exact expMeasure_one_integral_centered
  · intro i j
    change (∫ y:Fin n→ℝ,(y i-1)*(y j-1) ∂product n)=_
    by_cases hij:i=j
    · subst j
      have hs : (∫ y:ℝ,(y-1)^2 ∂expMeasure 1)=1 := by
        have hv := expMeasure_one_variance_centered
        rw [ProbabilityTheory.variance_eq_sub expMeasure_one_memLp_centered,
          expMeasure_one_integral_centered] at hv
        simpa using hv
      simp only [ite_true,←pow_two]
      rw [product,integral_comp_eval (μ:=fun _:Fin n=>expMeasure 1) (i:=i)
        (f:=fun y:ℝ=>(y-1)^2) (by fun_prop),hs]
    · rw [product,integral_mul_distinct_copies (g:=fun y:ℝ=>y-1) (h:=fun y:ℝ=>y-1)
        (by fun_prop) (by fun_prop) hij,
        expMeasure_one_integral_centered]
      simp [hij]

def exponentialDensity (y:ℝ) : ℝ := if 0≤y then Real.exp (-y) else 0

theorem exponentialDensity_eq_indicator : exponentialDensity=
    (Ici (0:ℝ)).indicator (fun y=>Real.exp (-y)) := by
  funext y
  by_cases hy:0≤y <;>simp [exponentialDensity,hy,Set.indicator]

@[fun_prop] theorem exponentialDensity_measurable : Measurable exponentialDensity := by
  rw [exponentialDensity_eq_indicator]
  exact (by fun_prop : Measurable (fun y:ℝ=>Real.exp (-y))).indicator measurableSet_Ici

theorem exponentialDensity_integrable : Integrable exponentialDensity volume := by
  have h : IntegrableOn (fun y:ℝ=>Real.exp (-y)) (Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) 0
  rw [exponentialDensity_eq_indicator]
  exact (integrable_indicator_iff measurableSet_Ici).mpr h

theorem exponentialDensity_nonneg (y:ℝ) : 0≤exponentialDensity y := by
  unfold exponentialDensity
  split_ifs <;>positivity

theorem expMeasure_eq_density : expMeasure 1=volume.withDensity
    (fun y=>ENNReal.ofReal (exponentialDensity y)) := by
  change volume.withDensity (exponentialPDF 1)=_
  congr 1
  funext y
  simp [exponentialPDF_eq,exponentialDensity]

def rawEuclideanProduct (n:ℕ) : Measure (Space n) :=
  (product n).map (MeasurableEquiv.toLp 2 (Fin n→ℝ))

def rawDensity (n:ℕ) (x:Space n) : ℝ≥0∞ :=
  ENNReal.ofReal (∏ i,exponentialDensity (x i))

theorem rawEuclideanProduct_eq_density (n:ℕ) :
    rawEuclideanProduct n=volume.withDensity (rawDensity n) := by
  unfold rawEuclideanProduct product
  simp_rw [expMeasure_eq_density]
  rw [pi_withDensity_ofReal (fun _:Fin n=>exponentialDensity)
    (fun _=>exponentialDensity_integrable) (fun _=>exponentialDensity_nonneg)]
  rw [map_withDensity_measurableEquiv _ _ _ (by fun_prop)]
  rw [show (volume : Measure (Fin n→ℝ)).map (MeasurableEquiv.toLp 2 (Fin n→ℝ))=
    (volume : Measure (Space n)) from (PiLp.volume_preserving_toLp (Fin n)).map_eq]
  rfl

theorem rawDensity_formula {n:ℕ} (x:Space n) : rawDensity n x=
    if ∀ i,0≤x i then ENNReal.ofReal (Real.exp (-(∑ i,x i))) else 0 := by
  classical
  unfold rawDensity
  by_cases hx:∀ i,0≤x i
  · rw [ite_eq_left hx]
    have hp : (∏ i,exponentialDensity (x i))=∏ i,Real.exp (-x i) := by
      apply Finset.prod_congr rfl
      intro i _
      simp [exponentialDensity,hx i]
    rw [hp,←Real.exp_sum,Finset.sum_neg_distrib]
  · obtain ⟨i,hi⟩ := not_forall.mp hx
    have hp : (∏ j,exponentialDensity (x j))=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [exponentialDensity,hi]
    simp [hx,hp]

theorem rawEuclideanProduct_logConcave (n:ℕ) : measureLogConcave (rawEuclideanProduct n) := by
  rw [rawEuclideanProduct_eq_density]
  apply measureLogConcave_withDensity_of_pointwise (by unfold rawDensity;fun_prop)
  intro x y t ht0 ht1
  rw [rawDensity_formula,rawDensity_formula,rawDensity_formula]
  by_cases hx:∀ i,0≤x i
  · by_cases hy:∀ i,0≤y i
    · have hz : ∀ i,0≤(t • x+(1-t) • y) i := by
        intro i
        change 0≤t*x i+(1-t)*y i
        exact add_nonneg (mul_nonneg ht0.le (hx i))
          (mul_nonneg (sub_pos.mpr ht1).le (hy i))
      rw [ite_eq_left hx,ite_eq_left hy,ite_eq_left hz,
        ←exp_neg_affine_eq_geometric (∑ i,x i) (∑ i,y i) t (1-t) ht0.le (sub_pos.mpr ht1).le]
      apply le_of_eq
      congr 2
      congr 1
      change t*(∑ i,x i)+(1-t)*(∑ i,y i)=∑ i,(t*x i+(1-t)*y i)
      simp only [Finset.sum_add_distrib,Finset.mul_sum]
    · simp only [hy,ite_false,ENNReal.zero_rpow_of_pos (sub_pos.mpr ht1),mul_zero]
      exact zero_le
  · simp only [hx,ite_false,ENNReal.zero_rpow_of_pos ht0,zero_mul]
    exact zero_le

def centerAffine (n:ℕ) : Space n≃ᴬ[ℝ]Space n :=
  ContinuousAffineEquiv.constVAdd ℝ (Space n) (WithLp.toLp 2 (fun _:Fin n=>(-1:ℝ)))

theorem centeredProduct_eq_raw_map (n:ℕ) : centeredProductMeasure n=
    (rawEuclideanProduct n).map (centerAffine n) := by
  rw [centeredProductMeasure,rawEuclideanProduct,Measure.map_map (centerAffine n).continuous.measurable
    (MeasurableEquiv.toLp 2 (Fin n→ℝ)).measurable]
  congr 1
  funext y
  apply PiLp.ext
  intro i
  change y i-1=(-1:ℝ)+y i
  ring

theorem centeredProduct_logConcave (n:ℕ) : measureLogConcave (centeredProductMeasure n) := by
  rw [centeredProduct_eq_raw_map]
  exact (rawEuclideanProduct_logConcave n).map_continuousAffineEquiv (centerAffine n)

theorem centeredProduct_admissible (n:ℕ) : admissibleMeasure (centeredProductMeasure n) :=
  ⟨centeredProduct_isProbability n,centeredProduct_logConcave n,centeredProduct_isIsotropic n⟩

end KLSImprovement.ProductAdmissible
#print axioms KLSImprovement.ProductAdmissible.centeredProduct_isIsotropic
#print axioms KLSImprovement.ProductAdmissible.centeredProduct_logConcave
#print axioms KLSImprovement.ProductAdmissible.centeredProduct_admissible

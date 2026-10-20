import ScalarQuadraticCubicJoint
import ProductCubicGramRows

/-! Residual cubic product kernels. The coordinate cubic is orthogonalized
against degree two; the mixed cubic is orthogonalized against A₁A₁. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace KLSImprovement.ProductJoint
open KLSImprovement.ProductCubic KLSImprovement.ProductPolynomial
open KLSImprovement.Exponential KLSImprovement.ExponentialCriticalGram
open KLSImprovement.ScalarJoint
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

def correction (m : ℕ) : ℝ := if m=2 then 2 else if m=3 then 9/2 else 0
def residualScalar (m : ℕ) (y : ℝ) : ℝ :=
  scalarAppell m y-correction m*scalarAppell (m-1) y

@[simp] theorem residualScalar_zero : residualScalar 0=(fun _=>1) := by
  funext y
  simp [residualScalar,correction,scalarAppell]

theorem residualScalar_memLp (m : ℕ) : MemLp (residualScalar m) 2 (expMeasure 1) :=
  (scalarAppell_memLp m).sub ((scalarAppell_memLp (m-1)).const_mul (correction m))

theorem residualScalar_mean (m : ℕ) :
    (∫ y,residualScalar m y ∂expMeasure 1)=if m=0 then 1 else 0 := by
  change (∫ y,scalarAppell m y-correction m*scalarAppell (m-1) y ∂expMeasure 1)=_
  rw [integral_sub (f:=scalarAppell m) (g:=fun y=>correction m*scalarAppell (m-1) y)
    (scalarAppell_integrable m)
    ((scalarAppell_integrable (m-1)).const_mul _),integral_const_mul,
    scalarAppell_mean,scalarAppell_mean]
  by_cases h0 : m=0
  · subst m
    norm_num [correction]
  · by_cases h1 : m=1
    · subst m
      norm_num [correction]
    · have hm : m-1≠0 := by omega
      simp [h0,hm]

def mixedKernel (m k : ℕ) : ℝ :=
  scalarKernel m k-correction k*scalarKernel m (k-1)

theorem mixedKernel_integral (m k : ℕ) :
    (∫ y,scalarAppell m y*residualScalar k y ∂expMeasure 1)=mixedKernel m k := by
  have he : (fun y=>scalarAppell m y*residualScalar k y)=
      (fun y=>scalarAppell m y*scalarAppell k y-
        correction k*(scalarAppell m y*scalarAppell (k-1) y)) := by
    funext y
    unfold residualScalar
    ring
  rw [he,integral_sub (f:=fun y=>scalarAppell m y*scalarAppell k y)
    (g:=fun y=>correction k*(scalarAppell m y*scalarAppell (k-1) y))
    ((scalarAppell_memLp m).integrable_mul (scalarAppell_memLp k))
    (((scalarAppell_memLp m).integrable_mul (scalarAppell_memLp (k-1))).const_mul _),
    integral_const_mul]
  rfl

def residualKernel (m k : ℕ) : ℝ :=
  mixedKernel m k-correction m*mixedKernel (m-1) k

theorem residualKernel_integral (m k : ℕ) :
    (∫ y,residualScalar m y*residualScalar k y ∂expMeasure 1)=residualKernel m k := by
  have he : (fun y=>residualScalar m y*residualScalar k y)=
      (fun y=>scalarAppell m y*residualScalar k y-
        correction m*(scalarAppell (m-1) y*residualScalar k y)) := by
    funext y
    unfold residualScalar
    ring
  rw [he,integral_sub (f:=fun y=>scalarAppell m y*residualScalar k y)
    (g:=fun y=>correction m*(scalarAppell (m-1) y*residualScalar k y))
    ((scalarAppell_memLp m).integrable_mul (residualScalar_memLp k))
    (((scalarAppell_memLp (m-1)).integrable_mul (residualScalar_memLp k)).const_mul _),
    integral_const_mul,mixedKernel_integral,mixedKernel_integral]
  rfl

theorem residualKernel_symm (m k : ℕ) : residualKernel m k=residualKernel k m := by
  rw [←residualKernel_integral,←residualKernel_integral]
  apply integral_congr_ae
  exact .of_forall (fun _=>mul_comm _ _)

@[simp] theorem residualKernel_zero_left (m : ℕ) :
    residualKernel 0 m=if m=0 then 1 else 0 := by
  rw [←residualKernel_integral,residualScalar_zero]
  simpa only [one_mul] using residualScalar_mean m

@[simp] theorem residualKernel_zero_right (m : ℕ) :
    residualKernel m 0=if m=0 then 1 else 0 := by
  rw [residualKernel_symm,residualKernel_zero_left]

@[simp] theorem mixedKernel_zero_left (m : ℕ) :
    mixedKernel 0 m=if m=0 then 1 else 0 := by
  rw [←mixedKernel_integral,scalarAppell_zero]
  simpa only [one_mul] using residualScalar_mean m

@[simp] theorem mixedKernel_zero_right (m : ℕ) :
    mixedKernel m 0=if m=0 then 1 else 0 := by
  simp [mixedKernel,correction]

theorem scalarKernel_succ_succ (m k : ℕ) :
    scalarKernel (m+1) (k+1)=
      ((m:ℝ)+1)*((k:ℝ)+1)*((m+k).factorial:ℝ) := by
  unfold scalarKernel
  simp only [scalarAppell_succ]
  exact integral_appell_mul m k

@[simp] theorem scalarKernel_three_two : scalarKernel 3 2=36 := by
  have h:=scalarKernel_succ_succ 2 1
  norm_num at h
  exact h
@[simp] theorem scalarKernel_two_three : scalarKernel 2 3=36 := by
  rw [scalarKernel_symm,scalarKernel_three_two]

@[simp] theorem residualKernel_one_one : residualKernel 1 1=1 := by
  norm_num [residualKernel,mixedKernel,correction]
@[simp] theorem residualKernel_two_two : residualKernel 2 2=4 := by
  norm_num [residualKernel,mixedKernel,correction]
@[simp] theorem residualKernel_one_two : residualKernel 1 2=0 := by
  norm_num [residualKernel,mixedKernel,correction]
@[simp] theorem residualKernel_two_one : residualKernel 2 1=0 := by
  rw [residualKernel_symm,residualKernel_one_two]
@[simp] theorem residualKernel_three_three : residualKernel 3 3=54 := by
  norm_num [residualKernel,mixedKernel,correction]
@[simp] theorem mixedKernel_one_one : mixedKernel 1 1=1 := by
  norm_num [mixedKernel,correction]
@[simp] theorem mixedKernel_one_two : mixedKernel 1 2=0 := by
  norm_num [mixedKernel,correction]
@[simp] theorem mixedKernel_two_three : mixedKernel 2 3=0 := by
  norm_num [mixedKernel,correction]

def residualBasis {n : ℕ} (I : Fin 3→Fin n) (y : Fin n→ℝ) : ℝ :=
  ∏ i,residualScalar (coordinateCount I i) (y i)
def residualGram {n : ℕ} (I J : Fin 3→Fin n) : ℝ :=
  ∏ i,residualKernel (coordinateCount I i) (coordinateCount J i)

theorem residualBasis_memLp {n : ℕ} (I : Fin 3→Fin n) :
    MemLp (residualBasis I) 2 (product n) := by
  have hi : Integrable (residualBasis I) (product n) :=
    Integrable.fintype_prod (fun i=>
      (residualScalar_memLp _).integrable (by norm_num : (1:ℝ≥0∞)≤2))
  apply (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).mpr
  have h := Integrable.fintype_prod (fun i:Fin n=>
    (residualScalar_memLp (coordinateCount I i)).integrable_sq)
  simpa only [residualBasis,Finset.prod_pow] using h

theorem residualGram_integral {n : ℕ} (I J : Fin 3→Fin n) :
    (∫ y,residualBasis I y*residualBasis J y ∂product n)=residualGram I J := by
  simp only [residualBasis,←Finset.prod_mul_distrib]
  calc
    _ = ∏ i,∫ y,residualScalar (coordinateCount I i) y*
        residualScalar (coordinateCount J i) y ∂expMeasure 1 :=
      integral_fintype_prod_eq_prod (μ:=fun _:Fin n=>expMeasure 1) _
    _ = _ := by simp only [residualKernel_integral];rfl

theorem residualGram_zero_of_outside {n : ℕ} (I J : Fin 3→Fin n) (a : Fin 3)
    (ha:J a∉coordinateSupport I) : residualGram I J=0 := by
  unfold residualGram
  apply Finset.prod_eq_zero (Finset.mem_univ (J a))
  rw [coordinateCount_zero_of_not_mem I ha,residualKernel_zero_left]
  simp [(coordinateCount_pos_at J a).ne']

theorem residualGram_restrict_product {n : ℕ} (I J : Fin 3→Fin n)
    (hJ:∀ a,J a∈coordinateSupport I) :
    residualGram I J=∏ i∈coordinateSupport I,
      residualKernel (coordinateCount I i) (coordinateCount J i) := by
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  have hJi:coordinateCount J i=0 := by
    unfold coordinateCount
    apply Finset.sum_eq_zero
    intro a _
    have hn:J a≠i := by intro he;exact hi (he ▸ hJ a)
    simp [hn]
  simp [coordinateCount_zero_of_not_mem I hi,hJi]

end KLSImprovement.ProductJoint
#print axioms KLSImprovement.ProductJoint.residualKernel_three_three
#print axioms KLSImprovement.ProductJoint.residualBasis_memLp
#print axioms KLSImprovement.ProductJoint.residualGram_integral

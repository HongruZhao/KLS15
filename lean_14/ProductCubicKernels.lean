import ActualAppellMoments
import ProductExponentialPolynomialMoments

/-! Genuine measure integrals of the product cubic Appell polynomials.
The covariance kernel is factored using the actual independent product law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace KLSImprovement.ProductCubic
open KLSImprovement.ExponentialMoments KLSImprovement.Exponential
open KLSImprovement.ProductPolynomial
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

def scalarAppell (m : ℕ) (y : ℝ) : ℝ :=
  if m=0 then 1 else appell (m-1) y

@[simp] theorem scalarAppell_zero : scalarAppell 0=(fun _=>1) := by
  funext y
  simp [scalarAppell]

@[simp] theorem scalarAppell_succ (m : ℕ) : scalarAppell (m+1)=appell m := by
  funext y
  simp [scalarAppell]

theorem scalarAppell_integrable (m : ℕ) :
    Integrable (scalarAppell m) (expMeasure 1) := by
  cases m with
  | zero => rw [scalarAppell_zero]; exact integrable_const (μ := expMeasure 1) (1:ℝ)
  | succ m => rw [scalarAppell_succ]; exact integrable_appell m

theorem scalarAppell_memLp (m : ℕ) :
    MemLp (scalarAppell m) 2 (expMeasure 1) := by
  cases m with
  | zero => rw [scalarAppell_zero]; exact memLp_const (μ := expMeasure 1) (p := 2) (1:ℝ)
  | succ m =>
    rw [scalarAppell_succ]
    apply (memLp_two_iff_integrable_sq (by unfold appell; fun_prop)).mpr
    exact integrable_appell_sq m

theorem scalarAppell_mean (m : ℕ) :
    (∫ y, scalarAppell m y ∂expMeasure 1) = if m=0 then 1 else 0 := by
  cases m with
  | zero => simp [scalarAppell]
  | succ m => simpa [scalarAppell] using integral_appell m

def scalarKernel (m k : ℕ) : ℝ :=
  ∫ y, scalarAppell m y * scalarAppell k y ∂expMeasure 1

theorem scalarKernel_symm (m k : ℕ) : scalarKernel m k=scalarKernel k m := by
  unfold scalarKernel
  congr 1
  funext y
  ring

@[simp] theorem scalarKernel_zero_left (m : ℕ) :
    scalarKernel 0 m=if m=0 then 1 else 0 := by
  simp only [scalarKernel, scalarAppell, ite_true, one_mul]
  exact scalarAppell_mean m

@[simp] theorem scalarKernel_zero_right (m : ℕ) :
    scalarKernel m 0=if m=0 then 1 else 0 := by
  rw [scalarKernel_symm, scalarKernel_zero_left]

@[simp] theorem scalarKernel_one_one : scalarKernel 1 1=1 := by
  have h:=integral_appell_sq 0
  simpa [scalarKernel, scalarAppell, pow_two] using h

@[simp] theorem scalarKernel_two_two : scalarKernel 2 2=8 := by
  have h:=integral_appell_sq 1
  norm_num [scalarKernel, scalarAppell, pow_two] at h ⊢
  exact h

@[simp] theorem scalarKernel_three_three : scalarKernel 3 3=216 := by
  have h:=integral_appell_sq 2
  norm_num [scalarKernel, scalarAppell, pow_two] at h ⊢
  exact h

@[simp] theorem scalarKernel_one_two : scalarKernel 1 2=2 := by
  have h3:Integrable (fun y:ℝ=>y^3) (expMeasure 1):=(expMeasure_one_nat_moment 3).1
  have h2:Integrable (fun y:ℝ=>y^2) (expMeasure 1):=(expMeasure_one_nat_moment 2).1
  have h1:=expMeasure_one_integrable_id
  have he : (fun y => scalarAppell 1 y*scalarAppell 2 y)=
      (fun y:ℝ=>y^3-3*y^2+2*y) := by
    funext y
    norm_num [scalarAppell, appell]
    ring
  have hs:Integrable (fun y:ℝ=>y^3-3*y^2) (expMeasure 1):=h3.sub (h2.const_mul 3)
  rw [scalarKernel,he,integral_add (f:=fun y:ℝ=>y^3-3*y^2)
    (g:=fun y:ℝ=>2*y) hs (h1.const_mul 2),
    integral_sub (f:=fun y:ℝ=>y^3) (g:=fun y:ℝ=>3*y^2) h3 (h2.const_mul 3)]
  simp only [integral_const_mul, (expMeasure_one_nat_moment 3).2,
    (expMeasure_one_nat_moment 2).2, expMeasure_one_integral_id]
  norm_num
  rw [integral_const_mul,expMeasure_one_integral_id]
  norm_num

@[simp] theorem scalarKernel_two_one : scalarKernel 2 1=2 := by
  rw [scalarKernel_symm,scalarKernel_one_two]

def coordinateCount {n : ℕ} (I : Fin 3 → Fin n) (i : Fin n) : ℕ :=
  ∑ a, if I a=i then 1 else 0

theorem coordinateCount_le_three {n : ℕ} (I : Fin 3 → Fin n) (i : Fin n) :
    coordinateCount I i≤3 := by
  calc
    _ ≤ ∑ _a : Fin 3, (1:ℕ) := Finset.sum_le_sum (fun a _ => by split_ifs <;> omega)
    _ = 3 := by simp

theorem coordinateCount_pos_at {n : ℕ} (I : Fin 3 → Fin n) (a : Fin 3) :
    0<coordinateCount I (I a) := by
  have h:=Finset.single_le_sum
    (f := fun b:Fin 3=>if I b=I a then (1:ℕ) else 0)
    (fun b _=>Nat.zero_le _) (Finset.mem_univ a)
  simp only [ite_true] at h
  unfold coordinateCount
  omega

def coordinateSupport {n : ℕ} (I : Fin 3 → Fin n) : Finset (Fin n) :=
  {I 0,I 1,I 2}

theorem coordinate_mem_support {n : ℕ} (I : Fin 3 → Fin n) (a : Fin 3) :
    I a∈coordinateSupport I := by
  fin_cases a <;> simp [coordinateSupport]

theorem coordinateCount_zero_of_not_mem {n : ℕ} (I : Fin 3 → Fin n) {i : Fin n}
    (hi:i∉coordinateSupport I) : coordinateCount I i=0 := by
  unfold coordinateCount
  apply Finset.sum_eq_zero
  intro a _
  have hn:I a≠i := by intro he; exact hi (he ▸ coordinate_mem_support I a)
  simp [hn]

def cubicBasis {n : ℕ} (I : Fin 3 → Fin n) (y : Fin n → ℝ) : ℝ :=
  ∏ i, scalarAppell (coordinateCount I i) (y i)

theorem cubicBasis_integrable {n : ℕ} (I : Fin 3 → Fin n) :
    Integrable (cubicBasis I) (product n) :=
  Integrable.fintype_prod (fun i => scalarAppell_integrable _)

theorem cubicBasis_memLp {n : ℕ} (I : Fin 3 → Fin n) :
    MemLp (cubicBasis I) 2 (product n) := by
  apply (memLp_two_iff_integrable_sq (cubicBasis_integrable I).aestronglyMeasurable).mpr
  have h:Integrable (fun y:Fin n→ℝ=>∏ i,(scalarAppell (coordinateCount I i) (y i))^2)
      (product n):=Integrable.fintype_prod (fun i:Fin n =>
        (scalarAppell_memLp (coordinateCount I i)).integrable_sq)
  simpa only [cubicBasis,Finset.prod_pow] using h

def cubicGram {n : ℕ} (I J : Fin 3 → Fin n) : ℝ :=
  ∏ i, scalarKernel (coordinateCount I i) (coordinateCount J i)

theorem cubicGram_integral {n : ℕ} (I J : Fin 3 → Fin n) :
    (∫ y, cubicBasis I y*cubicBasis J y ∂product n)=cubicGram I J := by
  simp only [cubicBasis, ←Finset.prod_mul_distrib]
  exact integral_fintype_prod_eq_prod
    (μ:=fun _ : Fin n=>expMeasure 1)
    (fun i y=>scalarAppell (coordinateCount I i) y*scalarAppell (coordinateCount J i) y)

theorem cubicGram_symm {n : ℕ} (I J : Fin 3 → Fin n) :
    cubicGram I J=cubicGram J I := by
  unfold cubicGram
  simp_rw [scalarKernel_symm]

theorem cubicGram_zero_of_outside {n : ℕ} (I J : Fin 3 → Fin n) (a : Fin 3)
    (ha:J a∉coordinateSupport I) : cubicGram I J=0 := by
  unfold cubicGram
  apply Finset.prod_eq_zero (Finset.mem_univ (J a))
  rw [coordinateCount_zero_of_not_mem I ha,scalarKernel_zero_left]
  simp [(coordinateCount_pos_at J a).ne']

theorem cubicGram_restrict_product {n : ℕ} (I J : Fin 3 → Fin n)
    (hJ:∀ a,J a∈coordinateSupport I) :
    cubicGram I J=∏ i∈coordinateSupport I,
      scalarKernel (coordinateCount I i) (coordinateCount J i) := by
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  have hJi:coordinateCount J i=0 := by
    unfold coordinateCount
    apply Finset.sum_eq_zero
    intro a _
    have hn:J a≠i := by intro he; exact hi (he ▸ hJ a)
    simp [hn]
  simp [coordinateCount_zero_of_not_mem I hi,hJi]

end KLSImprovement.ProductCubic
#print axioms KLSImprovement.ProductCubic.cubicGram_integral
#print axioms KLSImprovement.ProductCubic.cubicBasis_memLp

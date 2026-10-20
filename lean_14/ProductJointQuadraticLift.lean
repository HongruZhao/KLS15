import ProductQuadraticCubicJointBudget
import ProductCubicCenteredFormula

/-! Exact correction from residual cubics to original Appell cubics, and
its dimension-free ordered-index norm bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace KLSImprovement.ProductJoint
open KLSImprovement.ProductCubic KLSImprovement.ProductPolynomial
open KLSImprovement.Exponential
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

def quadraticLift {n : ℕ} (a : Fin n→Fin n→ℝ) (I : Fin 3→Fin n) : ℝ :=
  if I 0=I 1 then
    if I 0=I 2 then (9/2:ℝ)*a (I 0) (I 0) else 2*a (I 0) (I 2)
  else if I 0=I 2 then 2*a (I 0) (I 1)
  else if I 1=I 2 then 2*a (I 0) (I 1) else 0

theorem residualBasis_restrict {n : ℕ} (I : Fin 3→Fin n) (y : Fin n→ℝ) :
    residualBasis I y=∏ i∈coordinateSupport I,residualScalar (coordinateCount I i) (y i) := by
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  simp [coordinateCount_zero_of_not_mem I hi]

theorem pairBasis_restrict {n : ℕ} (I : Fin 2→Fin n) (y : Fin n→ℝ) :
    pairBasis I y=∏ i∈pairSupport I,scalarAppell (pairCount I i) (y i) := by
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  simp [pairCount_zero_of_not_mem I hi,scalarAppell]

theorem cubic_residual_difference_tuple {n : ℕ} (i j k : Fin n) (y : Fin n→ℝ) :
    cubicBasis ![i,j,k] y-residualBasis ![i,j,k] y=
      quadraticLift (fun a b=>pairBasis ![a,b] y) ![i,j,k] := by
  classical
  simp only [quadraticLift,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,cubicBasis_restrict,residualBasis_restrict,pairBasis_restrict]
  by_cases hij:i=j
  · subst j
    by_cases hik:i=k
    · subst k
      norm_num [coordinateSupport,pairSupport,coordinateCount_tuple,pairCount_tuple,
        residualScalar,correction,scalarAppell,appell]
    · norm_num [coordinateSupport,pairSupport,coordinateCount_tuple,pairCount_tuple,
        residualScalar,correction,scalarAppell,appell,hik,Ne.symm hik,
        Finset.prod_insert]
      ring
  · by_cases hik:i=k
    · subst k
      norm_num [coordinateSupport,pairSupport,coordinateCount_tuple,pairCount_tuple,
        residualScalar,correction,scalarAppell,appell,hij,Ne.symm hij,
        Finset.prod_insert]
      ring
    · by_cases hjk:j=k
      · subst k
        norm_num [coordinateSupport,pairSupport,coordinateCount_tuple,pairCount_tuple,
          residualScalar,correction,scalarAppell,appell,hij,Ne.symm hij,
          Finset.prod_insert]
        ring
      · norm_num [coordinateSupport,pairSupport,coordinateCount_tuple,pairCount_tuple,
          residualScalar,correction,scalarAppell,appell,hij,Ne.symm hij,
          hik,Ne.symm hik,hjk,Ne.symm hjk,Finset.prod_insert]

theorem cubic_residual_difference {n : ℕ} (I : Fin 3→Fin n) (y : Fin n→ℝ) :
    cubicBasis I y-residualBasis I y=
      quadraticLift (fun a b=>pairBasis ![a,b] y) I := by
  have he:I=![I 0,I 1,I 2] := by funext a;fin_cases a <;>simp
  simpa only [←he] using cubic_residual_difference_tuple (I 0) (I 1) (I 2) y

theorem quadraticLift_sq_tuple_le {n : ℕ} (a : Fin n→Fin n→ℝ) (i j k : Fin n) :
    (quadraticLift a ![i,j,k])^2≤(27/4:ℝ)*
      ((if i=j then (a i k)^2 else 0)+(if i=k then (a i j)^2 else 0)+
        (if j=k then (a i j)^2 else 0)) := by
  by_cases hij:i=j
  · subst j
    by_cases hik:i=k
    · subst k
      norm_num [quadraticLift]
      nlinarith
    · norm_num [quadraticLift,hik,Ne.symm hik]
      nlinarith [sq_nonneg (a i k)]
  · by_cases hik:i=k
    · subst k
      norm_num [quadraticLift,hij,Ne.symm hij]
      nlinarith [sq_nonneg (a i j)]
    · by_cases hjk:j=k
      · subst k
        norm_num [quadraticLift,hij,Ne.symm hij]
        nlinarith [sq_nonneg (a i j)]
      · norm_num [quadraticLift,hij,hik,hjk]

/-- The constant 81/4 is attained on the pure coordinate component. -/
theorem quadraticLift_square_sum_le {n : ℕ} (a : Fin n→Fin n→ℝ) :
    (∑ I,(quadraticLift a I)^2)≤(81/4:ℝ)*(∑ i,∑ j,(a i j)^2) := by
  classical
  have h1 : (∑ i:Fin n,∑ j:Fin n,∑ k:Fin n,if i=j then (a i k)^2 else 0)=
      ∑ i,∑ j,(a i j)^2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    simp
  have h2 : (∑ i:Fin n,∑ j:Fin n,∑ k:Fin n,if i=k then (a i j)^2 else 0)=
      ∑ i,∑ j,(a i j)^2 := by simp
  have h3 : (∑ i:Fin n,∑ j:Fin n,∑ k:Fin n,if j=k then (a i j)^2 else 0)=
      ∑ i,∑ j,(a i j)^2 := by simp
  rw [sum_triples]
  calc
    _ ≤ ∑ i,∑ j,∑ k,(27/4:ℝ)*
        ((if i=j then (a i k)^2 else 0)+(if i=k then (a i j)^2 else 0)+
          (if j=k then (a i j)^2 else 0)) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_le_sum (fun k _=>quadraticLift_sq_tuple_le a i j k)
    _ = _ := by
      simp_rw [←Finset.mul_sum,Finset.sum_add_distrib]
      rw [h1,h2,h3]
      ring

theorem integral_quadraticLift {n : ℕ} (f : (Fin n→ℝ)→ℝ) (I : Fin 3→Fin n) :
    (∫ y,f y*quadraticLift (fun a b=>pairBasis ![a,b] y) I ∂product n)=
      quadraticLift (fun a b=>∫ y,f y*pairBasis ![a,b] y ∂product n) I := by
  have hh (c : ℝ) (p : (Fin n→ℝ)→ℝ) :
      (∫ y,f y*(c*p y) ∂product n)=c*(∫ y,f y*p y ∂product n) := by
    have he : (fun y=>f y*(c*p y))=(fun y=>c*(f y*p y)) := by
      funext y
      ring
    rw [he,integral_const_mul]
  unfold quadraticLift
  split_ifs <;>simp only [hh,mul_zero,integral_zero]

theorem cubic_coefficient_eq_residual_add_lift {n : ℕ} {f : (Fin n→ℝ)→ℝ}
    (hf : MemLp f 2 (product n)) (I : Fin 3→Fin n) :
    (∫ y,f y*cubicBasis I y ∂product n)=
      (∫ y,f y*residualBasis I y ∂product n)+
        quadraticLift (fun a b=>∫ y,f y*pairBasis ![a,b] y ∂product n) I := by
  have hp : Integrable (fun y=>f y*quadraticLift (fun a b=>pairBasis ![a,b] y) I)
      (product n) := by
    have he : (fun y=>f y*quadraticLift (fun a b=>pairBasis ![a,b] y) I)=
        (fun y=>f y*cubicBasis I y-f y*residualBasis I y) := by
      funext y
      rw [←cubic_residual_difference]
      ring
    rw [he]
    exact (hf.integrable_mul (cubicBasis_memLp I)).sub
      (hf.integrable_mul (residualBasis_memLp I))
  have he : (fun y=>f y*cubicBasis I y)=
      (fun y=>f y*residualBasis I y+f y*quadraticLift (fun a b=>pairBasis ![a,b] y) I) := by
    funext y
    rw [←cubic_residual_difference]
    ring
  rw [he,integral_add (f:=fun y=>f y*residualBasis I y)
    (g:=fun y=>f y*quadraticLift (fun a b=>pairBasis ![a,b] y) I)
    (hf.integrable_mul (residualBasis_memLp I)) hp,integral_quadraticLift]

end KLSImprovement.ProductJoint
#print axioms KLSImprovement.ProductJoint.cubic_residual_difference
#print axioms KLSImprovement.ProductJoint.quadraticLift_square_sum_le
#print axioms KLSImprovement.ProductJoint.cubic_coefficient_eq_residual_add_lift

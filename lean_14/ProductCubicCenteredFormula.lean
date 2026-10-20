import ProductCubicSharpCap
import ActualProductCumulants

/-! The full cubic tensor inequality in the user's actual centered Euclidean
product law. The polynomial is written explicitly in the isotropic coordinates. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace KLSImprovement.ProductCubic
open KLS KLSImprovement.ProductPolynomial KLSImprovement.ActualProductCumulants
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

theorem cubicBasis_restrict {n : ℕ} (I : Fin 3→Fin n) (y:Fin n→ℝ) :
    cubicBasis I y=∏ i∈coordinateSupport I,scalarAppell (coordinateCount I i) (y i) := by
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  simp [coordinateCount_zero_of_not_mem I hi,scalarAppell]

def isotropicCubicKernel {n : ℕ} (I : Fin 3→Fin n) (x:Fin n→ℝ) : ℝ :=
  x (I 0)*x (I 1)*x (I 2)
  -(if I 0=I 1 then x (I 2) else 0)
  -(if I 0=I 2 then x (I 1) else 0)
  -(if I 1=I 2 then x (I 0) else 0)
  -(if I 0=I 1∧I 1=I 2 then 2 else 0)

theorem cubicBasis_tuple_formula {n : ℕ} (i j k:Fin n) (y:Fin n→ℝ) :
    cubicBasis ![i,j,k] y=isotropicCubicKernel ![i,j,k] (fun l=>y l-1) := by
  classical
  rw [cubicBasis_restrict]
  by_cases hij:i=j
  · subst j
    by_cases hik:i=k
    · subst k
      norm_num [coordinateSupport,coordinateCount_tuple,scalarAppell,
        KLSImprovement.Exponential.appell,isotropicCubicKernel]
      ring
    · norm_num [coordinateSupport,coordinateCount_tuple,scalarAppell,
        KLSImprovement.Exponential.appell,isotropicCubicKernel,hik,Ne.symm hik]
      ring
  · by_cases hik:i=k
    · subst k
      norm_num [coordinateSupport,coordinateCount_tuple,scalarAppell,
        KLSImprovement.Exponential.appell,isotropicCubicKernel,hij,Ne.symm hij]
      ring
    · by_cases hjk:j=k
      · subst k
        norm_num [coordinateSupport,coordinateCount_tuple,scalarAppell,
          KLSImprovement.Exponential.appell,isotropicCubicKernel,hij,Ne.symm hij]
        ring
      · norm_num [coordinateSupport,coordinateCount_tuple,scalarAppell,
          KLSImprovement.Exponential.appell,isotropicCubicKernel,hij,Ne.symm hij,
          hik,Ne.symm hik,hjk,Ne.symm hjk]
        ring

theorem cubicBasis_formula {n : ℕ} (I:Fin 3→Fin n) (y:Fin n→ℝ) :
    cubicBasis I y=isotropicCubicKernel I (fun l=>y l-1) := by
  have he:I=![I 0,I 1,I 2] := by funext a;fin_cases a <;>simp
  simpa only [←he] using cubicBasis_tuple_formula (I 0) (I 1) (I 2) y

def isotropicContractedCubic {n : ℕ} (T:(Fin 3→Fin n)→ℝ) (x:Space n) : ℝ :=
  ∑ I,T I*isotropicCubicKernel I (fun i=>x i)

theorem contractedCubic_centered_formula {n : ℕ} (T:(Fin 3→Fin n)→ℝ)
    (y:Fin n→ℝ) :
    contractedCubic T y=isotropicContractedCubic T (centeredProductMap n y) := by
  unfold contractedCubic isotropicContractedCubic
  apply Finset.sum_congr rfl
  intro I _
  rw [cubicBasis_formula]
  rfl

theorem centered_cubic_integral_transport {n : ℕ} (T:(Fin 3→Fin n)→ℝ) :
    (∫ x,(isotropicContractedCubic T x)^2 ∂centeredProductMeasure n)=
      ∫ y,(contractedCubic T y)^2 ∂product n := by
  rw [centeredProductMeasure,integral_map (measurable_centeredProductMap n).aemeasurable
    (by unfold isotropicContractedCubic isotropicCubicKernel;fun_prop)]
  apply integral_congr_ae
  exact .of_forall (fun y=>by
    change (isotropicContractedCubic T (centeredProductMap n y))^2=(contractedCubic T y)^2
    rw [contractedCubic_centered_formula])

/-- The full raw cubic cap 216 for the actual centered product exponential.
The tensor is arbitrary; every ordered entry contributes to its stated norm. -/
theorem actual_centered_product_cubic_square_le_216 {n : ℕ} (T:(Fin 3→Fin n)→ℝ) :
    (∫ x,(isotropicContractedCubic T x)^2 ∂centeredProductMeasure n)≤
      216*(∑ I,(T I)^2) := by
  rw [centered_cubic_integral_transport]
  exact product_cubic_square_le_216 T

theorem actual_centered_product_cubic_normalized_cap_six {n : ℕ}
    (T:(Fin 3→Fin n)→ℝ) :
    (∫ x,(isotropicContractedCubic T x)^2 ∂centeredProductMeasure n)/(Nat.factorial 3:ℝ)^2≤
      6*(∑ I,(T I)^2) := by
  rw [centered_cubic_integral_transport]
  exact product_cubic_normalized_square_le_six T

theorem actual_centered_product_cubic_coordinate_attains {n : ℕ} (i:Fin n) :
    (∫ x,(isotropicContractedCubic (coordinateTensor i) x)^2
      ∂centeredProductMeasure n)/(Nat.factorial 3:ℝ)^2=6 := by
  rw [centered_cubic_integral_transport,product_cubic_coordinate_attains]
  norm_num

end KLSImprovement.ProductCubic
#print axioms KLSImprovement.ProductCubic.actual_centered_product_cubic_square_le_216
#print axioms KLSImprovement.ProductCubic.actual_centered_product_cubic_normalized_cap_six
#print axioms KLSImprovement.ProductCubic.actual_centered_product_cubic_coordinate_attains

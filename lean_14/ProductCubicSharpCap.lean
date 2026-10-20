import ProductCubicGramRows
import FiniteGramRowBound

/-! The exact full cubic tensor cap for the actual independent exponential
product, in every finite dimension. All ordered indices and multiplicities
are retained. The polynomial covariance bound is not assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace KLSImprovement.ProductCubic
open KLSImprovement.ProductPolynomial KLSImprovement.FiniteGram
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def contractedCubic {n : ℕ} (T : (Fin 3→Fin n)→ℝ) (y : Fin n→ℝ) : ℝ :=
  ∑ I,T I*cubicBasis I y

theorem contractedCubic_memLp {n : ℕ} (T : (Fin 3→Fin n)→ℝ) :
    MemLp (contractedCubic T) 2 (product n) := by
  exact memLp_finsetSum _ (fun I _=>(cubicBasis_memLp I).const_mul (T I))

theorem contractedCubic_square_expansion {n : ℕ} (T : (Fin 3→Fin n)→ℝ)
    (y : Fin n→ℝ) :
    (contractedCubic T y)^2=
      ∑ I,∑ J,(T I*T J)*(cubicBasis I y*cubicBasis J y) := by
  simp only [contractedCubic,pow_two,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  ring

theorem contractedCubic_square_integral {n : ℕ} (T : (Fin 3→Fin n)→ℝ) :
    (∫ y,(contractedCubic T y)^2 ∂product n)=
      ∑ I,∑ J,T I*T J*cubicGram I J := by
  have hi (I J:Fin 3→Fin n) :
      Integrable (fun y=>(T I*T J)*(cubicBasis I y*cubicBasis J y)) (product n) :=
    ((cubicBasis_memLp I).integrable_mul (cubicBasis_memLp J)).const_mul (T I*T J)
  simp_rw [contractedCubic_square_expansion]
  rw [integral_finsetSum _ (fun I _=>integrable_finsetSum _ (fun J _=>hi I J))]
  apply Finset.sum_congr rfl
  intro I _
  rw [integral_finsetSum _ (fun J _=>hi I J)]
  apply Finset.sum_congr rfl
  intro J _
  rw [integral_const_mul,cubicGram_integral]

/-- Full ordered cubic tensor bound 216 = (3!)²*6 for the actual product law.
No rank one restriction or moment hypothesis appears in this statement. -/
theorem product_cubic_square_le_216 {n : ℕ} (T : (Fin 3→Fin n)→ℝ) :
    (∫ y,(contractedCubic T y)^2 ∂product n)≤216*(∑ I,(T I)^2) := by
  rw [contractedCubic_square_integral]
  exact symmetric_abs_row_quadratic_bound cubicGram cubicGram_symm cubicGram_abs_row_le T

theorem product_cubic_normalized_square_le_six {n : ℕ} (T : (Fin 3→Fin n)→ℝ) :
    (∫ y,(contractedCubic T y)^2 ∂product n)/(Nat.factorial 3:ℝ)^2≤6*(∑ I,(T I)^2) := by
  have h:=product_cubic_square_le_216 T
  norm_num at h ⊢
  linarith

def coordinateTensor {n : ℕ} (i : Fin n) (I : Fin 3→Fin n) : ℝ :=
  if I=(fun _=>i) then 1 else 0

theorem coordinateTensor_square_sum {n : ℕ} (i : Fin n) :
    (∑ I,(coordinateTensor i I)^2)=1 := by
  classical
  simp [coordinateTensor]

theorem contractedCubic_coordinate {n : ℕ} (i : Fin n) :
    contractedCubic (coordinateTensor i)=cubicBasis (fun _=>i) := by
  classical
  funext y
  simp [contractedCubic,coordinateTensor]

theorem cubicGram_coordinate_diagonal {n : ℕ} (i : Fin n) :
    cubicGram (fun _=>i) (fun _=>i)=216 := by
  have he:(fun _ : Fin 3=>i)=![i,i,i] := by funext a;fin_cases a <;>simp
  rw [he,cubicGram_restrict_product _ _ (fun a=>coordinate_mem_support _ a)]
  norm_num [coordinateSupport,coordinateCount_tuple]

/-- The coordinate cubic attains 216, proving the normalized product cap six
is optimal in each positive dimension. -/
theorem product_cubic_coordinate_attains {n : ℕ} (i : Fin n) :
    (∫ y,(contractedCubic (coordinateTensor i) y)^2 ∂product n)=216 := by
  rw [contractedCubic_coordinate]
  simpa only [pow_two] using
    (cubicGram_integral (fun _=>i) (fun _=>i)).trans (cubicGram_coordinate_diagonal i)

theorem product_cubic_cap_is_sharp {n : ℕ} (i : Fin n) {C : ℝ}
    (hC:∀ T:(Fin 3→Fin n)→ℝ,
      (∫ y,(contractedCubic T y)^2 ∂product n)/(Nat.factorial 3:ℝ)^2≤C*(∑ I,(T I)^2)) :
    6≤C := by
  have h:=hC (coordinateTensor i)
  rw [product_cubic_coordinate_attains,coordinateTensor_square_sum] at h
  norm_num at h
  exact h

end KLSImprovement.ProductCubic
#print axioms KLSImprovement.ProductCubic.product_cubic_square_le_216
#print axioms KLSImprovement.ProductCubic.product_cubic_normalized_square_le_six
#print axioms KLSImprovement.ProductCubic.product_cubic_coordinate_attains
#print axioms KLSImprovement.ProductCubic.product_cubic_cap_is_sharp

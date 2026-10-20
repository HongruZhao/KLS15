import ProductCubicObservation
import ActualCubicPolynomialFormula
import ActualProductAdmissible

/-! The sharp cubic cap through KLS15's original normalized tilt-derivative
interface, specialized to the actual centered product exponential law.
Admissibility, polynomial correspondence and the estimate are all proved. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal
namespace KLSImprovement.ProductCubic
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSImprovement.ActualProductCumulants KLSImprovement.CubicFormula
open KLSImprovement.ProductAdmissible
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
local instance (n:ℕ) : IsProbabilityMeasure (centeredProductMeasure n) :=
  centeredProduct_isProbability n

theorem centeredProduct_memLp_coordinate_triple {n:ℕ} (i j k:Fin n) :
    MemLp (fun x:Space n=>x i*x j*x k) 2 (centeredProductMeasure n) := by
  apply ((centeredProduct_logConcave n).memLp_two_norm_pow 3).mono' (by fun_prop)
  exact .of_forall (fun x=>by
    simp only [norm_mul]
    calc
      ‖x i‖*‖x j‖*‖x k‖≤‖x‖*‖x‖*‖x‖ := by
        gcongr <;>exact PiLp.norm_apply_le x _
      _=‖x‖^3 := by ring)

theorem actual_product_cubic_coefficient_eq_integral_tuple {n:ℕ}
    {f:Space n→ℝ} (hf:MemLp f 2 (centeredProductMeasure n)) (i j k:Fin n) :
    actualAppellCoefficient (centeredProductMeasure n) f 3 ![i,j,k]=
      ∫ x,f x*isotropicCubicKernel ![i,j,k] (fun l=>x l) ∂centeredProductMeasure n := by
  classical
  let μ := centeredProductMeasure n
  let a : ℝ := if j=k then 1 else 0
  let b : ℝ := if i=j then 1 else 0
  let c : ℝ := if i=k then 1 else 0
  let q : ℝ := if i=j∧j=k then 2 else 0
  have h0 : Integrable (fun x=>f x*(x i*x j*x k)) μ :=
    hf.integrable_mul (centeredProduct_memLp_coordinate_triple i j k)
  have h1 : Integrable (fun x=>a*(f x*x i)) μ :=
    (hf.integrable_mul ((centeredProduct_isIsotropic n).memLp_coordinate i)).const_mul a
  have h2 : Integrable (fun x=>b*(f x*x k)) μ :=
    (hf.integrable_mul ((centeredProduct_isIsotropic n).memLp_coordinate k)).const_mul b
  have h3 : Integrable (fun x=>c*(f x*x j)) μ :=
    (hf.integrable_mul ((centeredProduct_isIsotropic n).memLp_coordinate j)).const_mul c
  have h4 : Integrable (fun x=>q*f x) μ :=
    (hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).const_mul q
  have hp : (fun x:Space n=>f x*isotropicCubicKernel ![i,j,k] (fun l=>x l))=
      (fun x=>f x*(x i*x j*x k)-a*(f x*x i)-b*(f x*x k)-c*(f x*x j)-q*f x) := by
    funext x
    change f x*(x i*x j*x k-(if i=j then x k else 0)-(if i=k then x j else 0)
      -(if j=k then x i else 0)-(if i=j∧j=k then 2 else 0))=_
    dsimp only [a,b,c,q]
    split_ifs <;>ring
  have h01 : Integrable (fun x=>f x*(x i*x j*x k)-a*(f x*x i)) μ := h0.sub h1
  have h012 : Integrable (fun x=>f x*(x i*x j*x k)-a*(f x*x i)-b*(f x*x k)) μ := h01.sub h2
  have h0123 : Integrable
      (fun x=>f x*(x i*x j*x k)-a*(f x*x i)-b*(f x*x k)-c*(f x*x j)) μ := h012.sub h3
  change actualAppellCoefficient μ f 3 ![i,j,k]=
    ∫ x,f x*isotropicCubicKernel ![i,j,k] (fun l=>x l) ∂μ
  rw [hp,integral_sub h0123 h4,
    integral_sub h012 h3,integral_sub h01 h2,
    integral_sub h0 h1,integral_const_mul,integral_const_mul,integral_const_mul,integral_const_mul]
  have he0 : (∫ x:Space n,x i*f x*(x j*x k) ∂μ)=∫ x,f x*(x i*x j*x k) ∂μ := by
    apply integral_congr_ae
    exact .of_forall (fun x=>by ring)
  have he1 : (∫ x:Space n,x i*f x ∂μ)=∫ x,f x*x i ∂μ := by
    apply integral_congr_ae
    exact .of_forall (fun x=>by ring)
  rw [actualAppellCoefficient_three_moment_formula (centeredProduct_logConcave n)
    (centeredProduct_isIsotropic n) hf,centeredProduct_triple_moment]
  change (∫ x:Space n,x i*f x*(x j*x k) ∂μ)-(∫ x:Space n,x i*f x ∂μ)*a
    -c*(∫ x:Space n,f x*x j ∂μ)-b*(∫ x:Space n,f x*x k ∂μ)-q*(∫ x:Space n,f x ∂μ)=_
  rw [he0,he1]
  ring

/-- Exact correspondence with the original Appell definition for every
ordered cubic index, without an assumed admissibility premise. -/
theorem actual_product_cubic_coefficient_eq_integral {n:ℕ}
    {f:Space n→ℝ} (hf:MemLp f 2 (centeredProductMeasure n)) (I:Fin 3→Fin n) :
    actualAppellCoefficient (centeredProductMeasure n) f 3 I=
      ∫ x,f x*isotropicCubicKernel I (fun l=>x l) ∂centeredProductMeasure n := by
  have he : I=![I 0,I 1,I 2] := by funext a;fin_cases a <;>simp
  simpa only [←he] using actual_product_cubic_coefficient_eq_integral_tuple hf (I 0) (I 1) (I 2)

/-- Sharp raw cubic observation cap 216, in the original KLS15 interface. -/
theorem actual_product_appell_energy_three_le_216_integral {n:ℕ}
    {f:Space n→ℝ} (hf:MemLp f 2 (centeredProductMeasure n)) :
    actualAppellEnergy (centeredProductMeasure n) f 3≤
      216*(∫ x,(f x)^2 ∂centeredProductMeasure n) := by
  unfold actualAppellEnergy
  simp_rw [actual_product_cubic_coefficient_eq_integral hf]
  exact actual_centered_product_cubic_observation_le_216 hf

/-- The normalized original Appell cap is six, since (3!)²=36. -/
theorem actual_product_appell_energy_three_le_six_integral {n:ℕ}
    {f:Space n→ℝ} (hf:MemLp f 2 (centeredProductMeasure n)) :
    actualAppellEnergy (centeredProductMeasure n) f 3/(Nat.factorial 3:ℝ)^2≤
      6*(∫ x,(f x)^2 ∂centeredProductMeasure n) := by
  have h := actual_product_appell_energy_three_le_216_integral hf
  norm_num at h ⊢
  linarith

theorem actual_product_appell_energy_three_le_six_norm {n:ℕ}
    (f:Lp ℝ 2 (centeredProductMeasure n)) :
    actualAppellEnergy (centeredProductMeasure n) f 3/(Nat.factorial 3:ℝ)^2≤6*‖f‖^2 := by
  rw [actualLp_norm_sq_eq_integral]
  exact actual_product_appell_energy_three_le_six_integral (Lp.memLp f)

theorem centered_coordinate_cubic_square {n:ℕ} (i:Fin n) :
    (∫ x:Space n,(isotropicCubicKernel (fun _:Fin 3=>i) (fun l=>x l))^2
      ∂centeredProductMeasure n)=216 := by
  have h := centered_cubic_integral_transport (coordinateTensor i)
  rw [product_cubic_coordinate_attains] at h
  simpa [isotropicContractedCubic,coordinateTensor] using h

theorem actual_product_coordinate_cubic_energy {n:ℕ} (i:Fin n) :
    actualAppellEnergy (centeredProductMeasure n)
      (fun x=>isotropicCubicKernel (fun _:Fin 3=>i) (fun l=>x l)) 3=216^2 := by
  let f : Space n→ℝ := fun x=>isotropicCubicKernel (fun _:Fin 3=>i) (fun l=>x l)
  have hf : MemLp f 2 (centeredProductMeasure n) := isotropicCubicKernel_memLp _
  have hc : actualAppellCoefficient (centeredProductMeasure n) f 3 (fun _=>i)=216 := by
    rw [actual_product_cubic_coefficient_eq_integral hf]
    simpa only [f,pow_two] using centered_coordinate_cubic_square i
  have hlo : 216^2≤actualAppellEnergy (centeredProductMeasure n) f 3 := by
    rw [actualAppellEnergy]
    rw [←hc]
    exact Finset.single_le_sum (fun I _=>sq_nonneg _) (Finset.mem_univ (fun _:Fin 3=>i))
  have hhi := actual_product_appell_energy_three_le_216_integral hf
  change actualAppellEnergy (centeredProductMeasure n) f 3=216^2
  change actualAppellEnergy (centeredProductMeasure n) f 3≤216*
    (∫ x:Space n,(isotropicCubicKernel (fun _:Fin 3=>i) (fun l=>x l))^2
      ∂centeredProductMeasure n) at hhi
  rw [centered_coordinate_cubic_square] at hhi
  exact le_antisymm (by norm_num at hhi ⊢;exact hhi) hlo

/-- No smaller normalized cap can hold in any positive product dimension. -/
theorem actual_product_appell_cubic_cap_is_sharp {n:ℕ} (i:Fin n) {C:ℝ}
    (hC:∀ f:Space n→ℝ,MemLp f 2 (centeredProductMeasure n)→
      actualAppellEnergy (centeredProductMeasure n) f 3/(Nat.factorial 3:ℝ)^2≤
        C*(∫ x,(f x)^2 ∂centeredProductMeasure n)) : 6≤C := by
  have h := hC (fun x=>isotropicCubicKernel (fun _:Fin 3=>i) (fun l=>x l))
    (isotropicCubicKernel_memLp _)
  rw [actual_product_coordinate_cubic_energy,centered_coordinate_cubic_square] at h
  norm_num at h
  linarith

end KLSImprovement.ProductCubic
#print axioms KLSImprovement.ProductCubic.actual_product_cubic_coefficient_eq_integral
#print axioms KLSImprovement.ProductCubic.actual_product_appell_energy_three_le_six_integral
#print axioms KLSImprovement.ProductCubic.actual_product_appell_energy_three_le_six_norm
#print axioms KLSImprovement.ProductCubic.actual_product_coordinate_cubic_energy
#print axioms KLSImprovement.ProductCubic.actual_product_appell_cubic_cap_is_sharp

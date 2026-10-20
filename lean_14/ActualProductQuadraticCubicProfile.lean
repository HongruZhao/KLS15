import ProductQuadraticCubicProfile
import ActualProductCubicCap
import ActualAppellQuadraticSeed
import ActualCubicSeedObstruction

/-! The full joint product inequality through the original Appell
definitions. The actual centered product law discharges admissibility. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace KLSImprovement.ActualProductJoint
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSImprovement.ProductCubic KLSImprovement.ProductJoint
open KLSImprovement.ActualProductCumulants KLSImprovement.ProductAdmissible
open KLSImprovement.ProductPolynomial
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
local instance (n : ℕ) : IsProbabilityMeasure (centeredProductMeasure n) :=
  centeredProduct_isProbability n

def centeredPairKernel {n : ℕ} (I : Fin 2→Fin n) (x : Space n) : ℝ :=
  x (I 0)*x (I 1)-(if I 0=I 1 then 1 else 0)

theorem pairBasis_tuple_formula {n : ℕ} (i j : Fin n) (y : Fin n→ℝ) :
    pairBasis ![i,j] y=centeredPairKernel ![i,j] (centeredProductMap n y) := by
  classical
  rw [pairBasis_restrict]
  by_cases hij:i=j
  · subst j
    norm_num [pairSupport,pairCount_tuple,scalarAppell,KLSImprovement.Exponential.appell,
      centeredPairKernel,centeredProductMap]
    ring
  · norm_num [pairSupport,pairCount_tuple,scalarAppell,KLSImprovement.Exponential.appell,
      centeredPairKernel,centeredProductMap,hij,Ne.symm hij,Finset.prod_insert]

theorem pairBasis_formula {n : ℕ} (I : Fin 2→Fin n) (y : Fin n→ℝ) :
    pairBasis I y=centeredPairKernel I (centeredProductMap n y) := by
  have he:I=![I 0,I 1] := by funext a;fin_cases a <;>simp
  simpa only [←he] using pairBasis_tuple_formula (I 0) (I 1) y

theorem actual_product_quadratic_coefficient_eq_integral {n : ℕ}
    {f : Space n→ℝ} (hf : MemLp f 2 (centeredProductMeasure n)) (I : Fin 2→Fin n) :
    actualAppellCoefficient (centeredProductMeasure n) f 2 I=
      ∫ x,f x*centeredPairKernel I x ∂centeredProductMeasure n := by
  let μ:=centeredProductMeasure n
  let δ:ℝ:=if I 0=I 1 then 1 else 0
  have hν:=centeredProduct_admissible n
  have hprod : MemLp (fun x:Space n=>x (I 0)*x (I 1)) 2 μ :=
    hν.quadraticVarianceEight_unconditional.memLp_coordinate_mul (I 0) (I 1)
  have hi : Integrable (fun x:Space n=>δ*f x) μ :=
    (hf.integrable (by norm_num : (1:ℝ≥0∞)≤2)).const_mul δ
  have he : (fun x:Space n=>f x*centeredPairKernel I x)=
      (fun x=>f x*(x (I 0)*x (I 1))-δ*f x) := by
    funext x
    unfold centeredPairKernel
    dsimp only [δ]
    ring
  rw [actualAppellCoefficient_two_eq_quadraticCovariance hν hf,quadraticCovarianceMatrix,
    covariance_eq_sub hf hprod,hν.isotropic.integral_coordinate_mul]
  change (∫ x,f x*(x (I 0)*x (I 1)) ∂μ)-(∫ x,f x ∂μ)*δ=
    ∫ x,f x*centeredPairKernel I x ∂μ
  rw [he,integral_sub (f:=fun x:Space n=>f x*(x (I 0)*x (I 1)))
    (g:=fun x:Space n=>δ*f x) (hf.integrable_mul hprod) hi,integral_const_mul]
  ring

def rawPullback {n : ℕ} (f : Space n→ℝ) (y : Fin n→ℝ) : ℝ :=
  f (centeredProductMap n y)

theorem rawPullback_memLp {n : ℕ} {f : Space n→ℝ}
    (hf : MemLp f 2 (centeredProductMeasure n)) :
    MemLp (rawPullback f) 2 (product n) :=
  (memLp_map_measure_iff hf.aestronglyMeasurable
    (measurable_centeredProductMap n).aemeasurable).mp hf

theorem original_quadratic_coefficient_eq_raw {n : ℕ} {f : Space n→ℝ}
    (hf : MemLp f 2 (centeredProductMeasure n)) (I : Fin 2→Fin n) :
    actualAppellCoefficient (centeredProductMeasure n) f 2 I=
      ∫ y,rawPullback f y*pairBasis I y ∂product n := by
  rw [actual_product_quadratic_coefficient_eq_integral hf]
  have hk : Continuous (centeredPairKernel I) := by unfold centeredPairKernel;fun_prop
  have hm : AEStronglyMeasurable (fun x:Space n=>f x*centeredPairKernel I x)
      (centeredProductMeasure n) := hf.aestronglyMeasurable.mul hk.aestronglyMeasurable
  rw [centeredProductMeasure,integral_map (measurable_centeredProductMap n).aemeasurable hm]
  apply integral_congr_ae
  exact .of_forall (fun y=>by
    change f (centeredProductMap n y)*centeredPairKernel I (centeredProductMap n y)=
      rawPullback f y*pairBasis I y
    rw [pairBasis_formula]
    rfl)

theorem original_cubic_coefficient_eq_raw {n : ℕ} {f : Space n→ℝ}
    (hf : MemLp f 2 (centeredProductMeasure n)) (I : Fin 3→Fin n) :
    actualAppellCoefficient (centeredProductMeasure n) f 3 I=
      ∫ y,rawPullback f y*cubicBasis I y ∂product n := by
  rw [actual_product_cubic_coefficient_eq_integral hf]
  have hm : AEStronglyMeasurable
      (fun x:Space n=>f x*isotropicCubicKernel I (fun i=>x i)) (centeredProductMeasure n) :=
    hf.aestronglyMeasurable.mul (isotropicCubicKernel_memLp I).aestronglyMeasurable
  rw [centeredProductMeasure,integral_map (measurable_centeredProductMap n).aemeasurable hm]
  apply integral_congr_ae
  exact .of_forall (fun y=>by
    change f (centeredProductMap n y)*isotropicCubicKernel I (fun i=>y i-1)=
      rawPullback f y*cubicBasis I y
    rw [cubicBasis_formula]
    rfl)

theorem original_quadratic_energy_eq_raw {n : ℕ} {f : Space n→ℝ}
    (hf : MemLp f 2 (centeredProductMeasure n)) :
    actualAppellEnergy (centeredProductMeasure n) f 2=quadraticEnergy (rawPullback f) := by
  unfold actualAppellEnergy quadraticEnergy
  simp_rw [original_quadratic_coefficient_eq_raw hf]

theorem original_cubic_energy_eq_raw {n : ℕ} {f : Space n→ℝ}
    (hf : MemLp f 2 (centeredProductMeasure n)) :
    actualAppellEnergy (centeredProductMeasure n) f 3=cubicEnergy (rawPullback f) := by
  unfold actualAppellEnergy cubicEnergy
  simp_rw [original_cubic_coefficient_eq_raw hf]

theorem original_square_eq_raw {n : ℕ} {f : Space n→ℝ}
    (hf : MemLp f 2 (centeredProductMeasure n)) :
    (∫ x,(f x)^2 ∂centeredProductMeasure n)=∫ y,(rawPullback f y)^2 ∂product n := by
  have hm : AEStronglyMeasurable (fun x:Space n=>(f x)^2)
      (centeredProductMeasure n) := hf.aestronglyMeasurable.pow 2
  rw [centeredProductMeasure,integral_map (measurable_centeredProductMap n).aemeasurable hm]
  rfl

/-- Sharp full product benchmark profile in KLS15's actual coefficient
interface. Its maximum is 216 at quadratic energy six for unit tests. -/
theorem actual_product_quadratic_cubic_sqrt_profile {n : ℕ} {f : Space n→ℝ}
    (hf : MemLp f 2 (centeredProductMeasure n)) :
    Real.sqrt (actualAppellEnergy (centeredProductMeasure n) f 3)≤
      (9/2:ℝ)*Real.sqrt (actualAppellEnergy (centeredProductMeasure n) f 2)+
        Real.sqrt (54*((∫ x,(f x)^2 ∂centeredProductMeasure n)-
          actualAppellEnergy (centeredProductMeasure n) f 2/8)) := by
  rw [original_quadratic_energy_eq_raw hf,original_cubic_energy_eq_raw hf,
    original_square_eq_raw hf]
  exact full_product_quadratic_cubic_sqrt_profile (rawPullback_memLp hf)

theorem actual_product_quadratic_cubic_squared_profile {n : ℕ} {f : Space n→ℝ}
    (hf : MemLp f 2 (centeredProductMeasure n)) :
    actualAppellEnergy (centeredProductMeasure n) f 3≤
      ((9/2:ℝ)*Real.sqrt (actualAppellEnergy (centeredProductMeasure n) f 2)+
        Real.sqrt (54*((∫ x,(f x)^2 ∂centeredProductMeasure n)-
          actualAppellEnergy (centeredProductMeasure n) f 2/8)))^2 := by
  rw [original_quadratic_energy_eq_raw hf,original_cubic_energy_eq_raw hf,
    original_square_eq_raw hf]
  exact full_product_quadratic_cubic_squared_profile (rawPullback_memLp hf)

/-- The sharp cap 216 with the quadratic mismatch retained as an explicit
nonnegative square, for the actual product law in every finite dimension. -/
theorem actual_product_cubic_cap_with_quadratic_defect {n : ℕ} {f : Space n→ℝ}
    (hf : MemLp f 2 (centeredProductMeasure n)) :
    actualAppellEnergy (centeredProductMeasure n) f 3+
      3*((3/2:ℝ)*Real.sqrt (actualAppellEnergy (centeredProductMeasure n) f 2)-
        Real.sqrt (54*((∫ x,(f x)^2 ∂centeredProductMeasure n)-
          actualAppellEnergy (centeredProductMeasure n) f 2/8)))^2≤
        216*(∫ x,(f x)^2 ∂centeredProductMeasure n) := by
  rw [original_quadratic_energy_eq_raw hf,original_cubic_energy_eq_raw hf,
    original_square_eq_raw hf]
  exact full_product_cubic_cap_with_quadratic_defect (rawPullback_memLp hf)

/-- Actual equality in the original-interface joint profile. -/
theorem actual_scalar_joint_profile_cubic_witness_attains :
    let f:=KLSImprovement.CubicSeedObstruction.cubicWitness
    Real.sqrt (actualAppellEnergy (centeredProductMeasure 1) f 3)=
      (9/2:ℝ)*Real.sqrt (actualAppellEnergy (centeredProductMeasure 1) f 2)+
        Real.sqrt (54*((∫ x,(f x)^2 ∂centeredProductMeasure 1)-
          actualAppellEnergy (centeredProductMeasure 1) f 2/8)) := by
  dsimp only
  rw [KLSImprovement.CubicSeedObstruction.cubicWitness_energy_three,
    KLSImprovement.CubicSeedObstruction.cubicWitness_energy_two,
    KLSImprovement.CubicSeedObstruction.cubicWitness_square]
  norm_num

end KLSImprovement.ActualProductJoint
#print axioms KLSImprovement.ActualProductJoint.actual_product_quadratic_coefficient_eq_integral
#print axioms KLSImprovement.ActualProductJoint.actual_product_quadratic_cubic_sqrt_profile
#print axioms KLSImprovement.ActualProductJoint.actual_product_quadratic_cubic_squared_profile
#print axioms KLSImprovement.ActualProductJoint.actual_product_cubic_cap_with_quadratic_defect
#print axioms KLSImprovement.ActualProductJoint.actual_scalar_joint_profile_cubic_witness_attains

import ProductCubicCenteredFormula

/-! The dual full cubic estimate for every L² test under the actual product
law. This is an integral theorem, with no assumed observation bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace KLSImprovement.ProductCubic
open KLS KLSImprovement.ProductPolynomial KLSImprovement.ActualProductCumulants
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem product_cubic_observation_le_216 {n:ℕ} {f:(Fin n→ℝ)→ℝ}
    (hf:MemLp f 2 (product n)) :
    (∑ I:Fin 3→Fin n,(∫ y,f y*cubicBasis I y ∂product n)^2)≤
      216*(∫ y,(f y)^2 ∂product n) := by
  let c : (Fin 3→Fin n)→ℝ := fun I=>∫ y,f y*cubicBasis I y ∂product n
  let S : ℝ := ∑ I,(c I)^2
  let P := contractedCubic c
  have hP : MemLp P 2 (product n) := contractedCubic_memLp c
  have hff := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf
  have hPP := (memLp_two_iff_integrable_sq hP.aestronglyMeasurable).mp hP
  have hfP : Integrable (fun y=>f y*P y) (product n) := hf.integrable_mul hP
  have hpair : (∫ y,f y*P y ∂product n)=S := by
    change (∫ y,f y*(∑ I,c I*cubicBasis I y) ∂product n)=_
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ (fun I _=>
      ((hf.integrable_mul (cubicBasis_memLp I)).const_mul (c I)).congr
        (.of_forall (fun y=>by simp only [Pi.mul_apply];ring)))]
    apply Finset.sum_congr rfl
    intro I _
    have he : (fun y=>f y*(c I*cubicBasis I y))=
        (fun y=>c I*(f y*cubicBasis I y)) := by funext y;ring
    rw [he,integral_const_mul]
    change c I*c I=(c I)^2
    ring
  have hnonneg : 0≤∫ y,(216*f y-P y)^2 ∂product n :=
    integral_nonneg (fun _=>sq_nonneg _)
  have hexpand : (∫ y,(216*f y-P y)^2 ∂product n)=
      46656*(∫ y,(f y)^2 ∂product n)-432*S+(∫ y,(P y)^2 ∂product n) := by
    have he : (fun y=>(216*f y-P y)^2)=
        (fun y=>46656*(f y)^2-432*(f y*P y)+(P y)^2) := by
      funext y;ring
    have hm : Integrable (fun y=>46656*(f y)^2-432*(f y*P y)) (product n) :=
      (hff.const_mul 46656).sub (hfP.const_mul 432)
    rw [he,integral_add hm hPP,
      integral_sub (hff.const_mul 46656) (hfP.const_mul 432),
      integral_const_mul,integral_const_mul,hpair]
  have hbound : (∫ y,(P y)^2 ∂product n)≤216*S := product_cubic_square_le_216 c
  rw [hexpand] at hnonneg
  change S≤216*(∫ y,(f y)^2 ∂product n)
  linarith

theorem isotropicCubicKernel_memLp {n:ℕ} (I:Fin 3→Fin n) :
    MemLp (fun x:Space n=>isotropicCubicKernel I (fun i=>x i)) 2
      (centeredProductMeasure n) := by
  unfold centeredProductMeasure
  apply (memLp_map_measure_iff (by unfold isotropicCubicKernel;fun_prop)
    (measurable_centeredProductMap n).aemeasurable).mpr
  exact MemLp.ae_eq (.of_forall (fun y=>cubicBasis_formula I y)) (cubicBasis_memLp I)

/-- Dual cubic observation estimate, using the actual centered Euclidean law
and every ordered coordinate coefficient. -/
theorem actual_centered_product_cubic_observation_le_216 {n:ℕ} {f:Space n→ℝ}
    (hf:MemLp f 2 (centeredProductMeasure n)) :
    (∑ I:Fin 3→Fin n,
      (∫ x,f x*isotropicCubicKernel I (fun i=>x i) ∂centeredProductMeasure n)^2)≤
      216*(∫ x,(f x)^2 ∂centeredProductMeasure n) := by
  have hfm : MemLp (fun y=>f (centeredProductMap n y)) 2 (product n) :=
    (memLp_map_measure_iff hf.aestronglyMeasurable
      (measurable_centeredProductMap n).aemeasurable).mp hf
  have he (I:Fin 3→Fin n) :
      (∫ x,f x*isotropicCubicKernel I (fun i=>x i) ∂centeredProductMeasure n)=
        ∫ y,f (centeredProductMap n y)*cubicBasis I y ∂product n := by
    have hm : AEStronglyMeasurable
        (fun x:Space n=>f x*isotropicCubicKernel I (fun i=>x i))
        (centeredProductMeasure n) :=
      hf.aestronglyMeasurable.mul (isotropicCubicKernel_memLp I).aestronglyMeasurable
    rw [centeredProductMeasure,integral_map
      (measurable_centeredProductMap n).aemeasurable hm]
    apply integral_congr_ae
    exact .of_forall (fun y=>by
      change f (centeredProductMap n y)*isotropicCubicKernel I (fun i=>y i-1)=
        f (centeredProductMap n y)*cubicBasis I y
      rw [cubicBasis_formula])
  have hs : (∫ x,(f x)^2 ∂centeredProductMeasure n)=
      ∫ y,(f (centeredProductMap n y))^2 ∂product n := by
    have hm : AEStronglyMeasurable (fun x=>(f x)^2) (centeredProductMeasure n) :=
      hf.aestronglyMeasurable.pow 2
    rw [centeredProductMeasure,integral_map
      (measurable_centeredProductMap n).aemeasurable hm]
  simp_rw [he]
  rw [hs]
  exact product_cubic_observation_le_216 hfm

end KLSImprovement.ProductCubic
#print axioms KLSImprovement.ProductCubic.product_cubic_observation_le_216
#print axioms KLSImprovement.ProductCubic.isotropicCubicKernel_memLp
#print axioms KLSImprovement.ProductCubic.actual_centered_product_cubic_observation_le_216

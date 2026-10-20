import ProductExponentialCharged

/-! The full covariance/mean-gradient charge for the actual centered
independent exponential product, in every finite dimension. The final
compact-core theorems assume only C1 regularity and compact support. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace KLSImprovement.Tensorization
open KLSImprovement.Exponential
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure law := isProbabilityMeasure_expMeasure (by norm_num)

theorem centered_exponential_finite_product_charged (n : ℕ)
    (f : (Fin n→ℝ)→ℝ) (hf : StronglyMeasurable f) {C D : ℝ} (hb : ∀ x,‖f x‖≤C)
    (hreg : ∀ i x,ContDiff ℝ 1 (fun t=>f (Function.update x i t)))
    (hc : ∀ i x,HasCompactSupport (fun t=>f (Function.update x i t)))
    (hd : ∀ i,StronglyMeasurable (coordinateDeriv f i))
    (hdb : ∀ i x,‖coordinateDeriv f i x‖≤D) :
    variance f (centeredProductLaw n)+
      (∑ i,((∫ x,x i*f x ∂centeredProductLaw n)-
        2*(∫ x,coordinateDeriv f i x ∂centeredProductLaw n))^2)+
      2*(∑ i,(∫ x,coordinateDeriv f i x ∂centeredProductLaw n)^2)≤
        4*(∫ x,∑ i,(coordinateDeriv f i x)^2 ∂centeredProductLaw n) := by
  let F:(Fin n→ℝ)→ℝ:=fun x=>f (centerCoordinates x)
  have hF:StronglyMeasurable F:=hf.comp_measurable centerCoordinates_measurable
  have hr (i:Fin n) (x:Fin n→ℝ) : ContDiff ℝ 1 (fun t=>F (Function.update x i t)) := by
    dsimp [F]
    simp_rw [centerCoordinates_update]
    exact (hreg i (centerCoordinates x)).comp (by fun_prop)
  have hcs (i:Fin n) (x:Fin n→ℝ) : HasCompactSupport (fun t=>F (Function.update x i t)) := by
    dsimp [F]
    simp_rw [centerCoordinates_update]
    simpa [Function.comp_def,Homeomorph.addRight,sub_eq_add_neg] using
      (hc i (centerCoordinates x)).comp_homeomorph (Homeomorph.addRight (-1:ℝ))
  have hdF (i:Fin n) : StronglyMeasurable (coordinateDeriv F i) := by
    rw [show coordinateDeriv F i=(fun x=>coordinateDeriv f i (centerCoordinates x)) from
      funext (coordinateDeriv_center f i)]
    exact (hd i).comp_measurable centerCoordinates_measurable
  have hdbF (i:Fin n) (x:Fin n→ℝ) : ‖coordinateDeriv F i x‖≤D := by
    rw [show coordinateDeriv F i x=coordinateDeriv f i (centerCoordinates x) from
      coordinateDeriv_center f i x]
    exact hdb i _
  have he:=exponential_finite_product_charged n F hF (fun x=>hb (centerCoordinates x)) hr hcs hdF hdbF
  have hvar:variance f (centeredProductLaw n)=variance F (productLaw n) :=
    variance_map hf.measurable.aemeasurable centerCoordinates_measurable.aemeasurable
  have hm (i:Fin n) : (∫ x,x i*f x ∂centeredProductLaw n)=
      ∫ x,(x i-1)*F x ∂productLaw n := by
    rw [integral_map (f:=fun x:Fin n→ℝ=>x i*f x) centerCoordinates_measurable.aemeasurable
      (((measurable_pi_apply i).stronglyMeasurable.mul hf).aestronglyMeasurable)]
    rfl
  have hb' (i:Fin n) : (∫ x,coordinateDeriv f i x ∂centeredProductLaw n)=
      ∫ x,coordinateDeriv F i x ∂productLaw n := by
    rw [integral_map centerCoordinates_measurable.aemeasurable (hd i).aestronglyMeasurable]
    apply integral_congr_ae
    exact .of_forall fun x=>(coordinateDeriv_center f i x).symm
  have henergy:(∫ x,∑ i,(coordinateDeriv f i x)^2 ∂centeredProductLaw n)=
      ∫ x,∑ i,(coordinateDeriv F i x)^2 ∂productLaw n := by
    rw [integral_map centerCoordinates_measurable.aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun x=>∑ i,(coordinateDeriv f i x)^2) (centeredProductLaw n))]
    apply integral_congr_ae
    exact .of_forall fun x=>by
      apply Finset.sum_congr rfl
      intro i _
      rw [show coordinateDeriv F i x=coordinateDeriv f i (centerCoordinates x) from
        coordinateDeriv_center f i x]
  rw [hvar,henergy]
  simp_rw [hm,hb']
  exact he

/-- Full retained charge on the ordinary compact C1 core. Every slice,
measurability and bound hypothesis is derived from these two assumptions. -/
theorem centered_exponential_product_charged_compact_core (n : ℕ)
    (f : (Fin n→ℝ)→ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    variance f (centeredProductLaw n)+
      (∑ i,((∫ x,x i*f x ∂centeredProductLaw n)-
        2*(∫ x,coordinateDeriv f i x ∂centeredProductLaw n))^2)+
      2*(∑ i,(∫ x,coordinateDeriv f i x ∂centeredProductLaw n)^2)≤
        4*(∫ x,∑ i,(coordinateDeriv f i x)^2 ∂centeredProductLaw n) := by
  obtain ⟨C,hC⟩:=hc.exists_bound_of_continuous hf.continuous
  obtain ⟨D,hD⟩:=(hc.fderiv ℝ).exists_bound_of_continuous (hf.continuous_fderiv one_ne_zero)
  have hd (i:Fin n) : Continuous (coordinateDeriv f i) := by
    rw [show coordinateDeriv f i=(fun x=>fderiv ℝ f x (Pi.single i 1)) from
      funext (coordinateDeriv_eq_fderiv f hf i)]
    exact (hf.continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const)
  apply centered_exponential_finite_product_charged n f hf.continuous.stronglyMeasurable hC
    (fun i x=>hf.comp (contDiff_update 1 x i))
    (fun i x=>hc.comp_isClosedEmbedding (isClosedEmbedding_update x i))
    (fun i=>(hd i).stronglyMeasurable)
  intro i x
  rw [coordinateDeriv_eq_fderiv f hf i x]
  calc
    ‖fderiv ℝ f x (Pi.single i 1)‖≤‖fderiv ℝ f x‖*‖(Pi.single i (1:ℝ):Fin n→ℝ)‖ :=
      (fderiv ℝ f x).le_opNorm _
    _=‖fderiv ℝ f x‖ := by simp only [Pi.norm_single,norm_one,mul_one]
    _≤D:=hD x

/-- The user's covariance-charge inequality, in every finite dimension.
No mean-gradient-zero assumption is needed for the coefficient one third. -/
theorem centered_exponential_product_covariance_charge (n : ℕ)
    (f : (Fin n→ℝ)→ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    variance f (centeredProductLaw n)+(1/3:ℝ)*
      (∑ i,(∫ x,x i*f x ∂centeredProductLaw n)^2)≤
        4*(∫ x,∑ i,(coordinateDeriv f i x)^2 ∂centeredProductLaw n) := by
  have he:=centered_exponential_product_charged_compact_core n f hf hc
  have hsum:(∑ i,(1/3:ℝ)*(∫ x,x i*f x ∂centeredProductLaw n)^2)≤
      ∑ i,(((∫ x,x i*f x ∂centeredProductLaw n)-
        2*(∫ x,coordinateDeriv f i x ∂centeredProductLaw n))^2+
        2*(∫ x,coordinateDeriv f i x ∂centeredProductLaw n)^2) := by
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg ((∫ x,x i*f x ∂centeredProductLaw n)-
      3*(∫ x,coordinateDeriv f i x ∂centeredProductLaw n))]
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hsum
  linarith

/-- On zero mean-gradient tests the covariance coefficient improves to one,
which supplies the sharp-four affine Schur condition with room to spare. -/
theorem centered_exponential_product_covariance_charge_of_mean_gradient_zero (n : ℕ)
    (f : (Fin n→ℝ)→ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hz : ∀ i,(∫ x,coordinateDeriv f i x ∂centeredProductLaw n)=0) :
    variance f (centeredProductLaw n)+(∑ i,(∫ x,x i*f x ∂centeredProductLaw n)^2)≤
      4*(∫ x,∑ i,(coordinateDeriv f i x)^2 ∂centeredProductLaw n) := by
  simpa only [hz,mul_zero,sub_zero,zero_pow (by norm_num : 2≠0),Finset.sum_const_zero,
    add_zero] using centered_exponential_product_charged_compact_core n f hf hc

end KLSImprovement.Tensorization
#print axioms KLSImprovement.Tensorization.centered_exponential_finite_product_charged
#print axioms KLSImprovement.Tensorization.centered_exponential_product_charged_compact_core
#print axioms KLSImprovement.Tensorization.centered_exponential_product_covariance_charge
#print axioms KLSImprovement.Tensorization.centered_exponential_product_covariance_charge_of_mean_gradient_zero

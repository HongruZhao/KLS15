import CenteredProductPoincare

/-! Retaining bounded conditional affine charges in the actual finite
product tensorization. The exponential specialization is separate. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace KLSImprovement.Tensorization
open KLSImprovement.Exponential
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure law := isProbabilityMeasure_expMeasure (by norm_num)

lemma square_le_of_norm_le {x B : ℝ} (h : ‖x‖≤B) : x^2≤B^2 := by
  have hB:0≤B := (norm_nonneg x).trans h
  have he:=(sq_le_sq₀ (norm_nonneg x) hB).mpr h
  simpa only [Real.norm_eq_abs,sq_abs] using he

/-- The variance tensorization retains the squares of the means of
conditional charges, by the scalar variance inequality (Jensen). -/
theorem finite_product_charged_energy_bound (n : ℕ) (f : (Fin n→ℝ)→ℝ)
    (hf : StronglyMeasurable f) {C D A B : ℝ} (hb : ∀ x,‖f x‖≤C)
    (q a b : Fin n→(Fin n→ℝ)→ℝ)
    (hq : ∀ i,StronglyMeasurable (q i)) (hqb : ∀ i x,‖q i x‖≤D)
    (ha : ∀ i,StronglyMeasurable (a i)) (hab : ∀ i x,‖a i x‖≤A)
    (hbmeas : ∀ i,StronglyMeasurable (b i)) (hbb : ∀ i x,‖b i x‖≤B)
    (hau : ∀ i x t,a i (Function.update x i t)=a i x)
    (hbu : ∀ i x t,b i (Function.update x i t)=b i x)
    (hslice : ∀ i x,variance (fun t=>f (Function.update x i t)) law+
      (a i x)^2+2*(b i x)^2≤∫ t,q i (Function.update x i t) ∂law) :
    variance f (productLaw n)+
      (∑ i,(∫ x,a i x ∂productLaw n)^2)+
      2*(∑ i,(∫ x,b i x ∂productLaw n)^2)≤
        ∫ x,∑ i,q i x ∂productLaw n := by
  let e : Fin n→(Fin n→ℝ)→ℝ := fun i x=>q i x-(a i x)^2-2*(b i x)^2
  have hqm (i) : MemLp (q i) 2 (productLaw n) :=
    MemLp.of_bound (hq i).aestronglyMeasurable D (.of_forall (hqb i))
  have ham (i) : MemLp (a i) 2 (productLaw n) :=
    MemLp.of_bound (ha i).aestronglyMeasurable A (.of_forall (hab i))
  have hbm (i) : MemLp (b i) 2 (productLaw n) :=
    MemLp.of_bound (hbmeas i).aestronglyMeasurable B (.of_forall (hbb i))
  have hem (i) : StronglyMeasurable (e i) :=
    ((hq i).sub ((ha i).pow 2)).sub (((hbmeas i).pow 2).const_mul 2)
  have heb (i) (x) : ‖e i x‖≤D+A^2+2*B^2 := by
    dsimp only [e]
    calc
      ‖q i x-(a i x)^2-2*(b i x)^2‖≤‖q i x‖+‖(a i x)^2‖+‖2*(b i x)^2‖ := by
        calc
          _≤‖q i x-(a i x)^2‖+‖2*(b i x)^2‖ := norm_sub_le _ _
          _≤_ := by gcongr;exact norm_sub_le _ _
      _≤D+A^2+2*B^2 := by
        rw [Real.norm_of_nonneg (sq_nonneg (a i x)),
          Real.norm_of_nonneg (show (0:ℝ)≤2*(b i x)^2 by positivity)]
        nlinarith [hqb i x,square_le_of_norm_le (hab i x),square_le_of_norm_le (hbb i x)]
  have heint (i) : Integrable (e i) (productLaw n) :=
    ((hqm i).integrable (by norm_num)).sub (ham i).integrable_sq |>.sub
      ((hbm i).integrable_sq.const_mul 2)
  have hE:=finite_product_energy_bound n f hf hb e hem heb (fun i x=>by
    have hqi:Integrable (fun t=>q i (Function.update x i t)) law :=
      (MemLp.of_bound ((hq i).comp_measurable (by fun_prop)).aestronglyMeasurable D
        (.of_forall fun t=>hqb i _) : MemLp _ 2 law).integrable (by norm_num)
    have he:(∫ t,e i (Function.update x i t) ∂law)=
        (∫ t,q i (Function.update x i t) ∂law)-(a i x)^2-2*(b i x)^2 := by
      dsimp only [e]
      simp_rw [hau,hbu]
      rw [integral_sub (f:=fun t=>q i (Function.update x i t)-(a i x)^2)
        (g:=fun _=>2*(b i x)^2) (hqi.sub (integrable_const _)) (integrable_const _),
        integral_sub (f:=fun t=>q i (Function.update x i t))
          (g:=fun _=>(a i x)^2) hqi (integrable_const _)]
      simp
    rw [he]
    linarith [hslice i x])
  have hi (i) : (∫ x,e i x ∂productLaw n)=
      (∫ x,q i x ∂productLaw n)-(∫ x,(a i x)^2 ∂productLaw n)-
        2*(∫ x,(b i x)^2 ∂productLaw n) := by
    unfold e
    rw [integral_sub (f:=fun x=>q i x-(a i x)^2) (g:=fun x=>2*(b i x)^2)
      (((hqm i).integrable (by norm_num)).sub (ham i).integrable_sq)
      ((hbm i).integrable_sq.const_mul 2),
      integral_sub (f:=fun x=>q i x) (g:=fun x=>(a i x)^2)
        ((hqm i).integrable (by norm_num)) (ham i).integrable_sq,
      integral_const_mul]
  have hja: (∑ i,(∫ x,a i x ∂productLaw n)^2)≤
      ∑ i,(∫ x,(a i x)^2 ∂productLaw n) := by
    apply Finset.sum_le_sum
    intro i _
    have he:=variance_nonneg (a i) (productLaw n)
    rw [variance_eq_sub (ham i)] at he
    simp only [Pi.pow_apply] at he
    linarith
  have hjb: (∑ i,(∫ x,b i x ∂productLaw n)^2)≤
      ∑ i,(∫ x,(b i x)^2 ∂productLaw n) := by
    apply Finset.sum_le_sum
    intro i _
    have he:=variance_nonneg (b i) (productLaw n)
    rw [variance_eq_sub (hbm i)] at he
    simp only [Pi.pow_apply] at he
    linarith
  rw [integral_finsetSum _ (fun i _=>heint i)] at hE
  simp_rw [hi] at hE
  rw [integral_finsetSum _ (fun i _=>(hqm i).integrable (by norm_num))]
  simp only [Finset.sum_sub_distrib,←Finset.mul_sum] at hE
  linarith

/-- Integrating after replacing one independent coordinate preserves the
actual product expectation. Integrability and measurability are explicit. -/
theorem integral_coordinate_resampling {n : ℕ} (g : (Fin n→ℝ)→ℝ)
    (hg : StronglyMeasurable g) (hgi : Integrable g (productLaw n)) (i : Fin n) :
    (∫ x,∫ t,g (Function.update x i t) ∂law ∂productLaw n)=
      ∫ x,g x ∂productLaw n := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    let e:=MeasurableEquiv.piFinSuccAbove (fun _:Fin (n+1)=>ℝ) i
    have he:MeasurePreserving e (productLaw (n+1)) (law.prod (productLaw n)) :=
      measurePreserving_piFinSuccAbove (fun _:Fin (n+1)=>law) i
    have hG:Integrable (fun p:ℝ×(Fin n→ℝ)=>g (e.symm p)) (law.prod (productLaw n)) :=
      (he.symm.integrable_comp hg.aestronglyMeasurable).mpr hgi
    have hu (p:ℝ×(Fin n→ℝ)) (t:ℝ) :
        Function.update (e.symm p) i t=e.symm (t,p.2) := by
      simp only [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
        Equiv.coe_fn_mk,Fin.update_insertNth]
    rw [←he.symm.integral_comp' (fun x=>∫ t,g (Function.update x i t) ∂law)]
    simp_rw [hu]
    let h:(Fin n→ℝ)→ℝ:=fun z=>∫ t,g (e.symm (t,z)) ∂law
    change (∫ p:ℝ×(Fin n→ℝ),h p.2 ∂law.prod (productLaw n))=_
    rw [integral_fun_snd h]
    simp only [measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]
    change (∫ z,∫ t,g (e.symm (t,z)) ∂law ∂productLaw n)=_
    rw [←integral_prod_symm _ hG]
    exact he.symm.integral_comp' g

end KLSImprovement.Tensorization
#print axioms KLSImprovement.Tensorization.finite_product_charged_energy_bound
#print axioms KLSImprovement.Tensorization.integral_coordinate_resampling

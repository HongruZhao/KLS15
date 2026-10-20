import ChargedFiniteProductTensorization

/-! Actual product-exponential charged Poincare inequality. Conditional
charges are genuine integrals; no moment, independence, or target bound is
an assumption. The test domain is the compact coordinate core. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace KLSImprovement.Tensorization
open KLSImprovement.Exponential KLSImprovement.ExponentialMoments
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure law := isProbabilityMeasure_expMeasure (by norm_num)

def conditionalCovariance {n : ℕ} (f : (Fin n→ℝ)→ℝ) (i : Fin n) (x : Fin n→ℝ) : ℝ :=
  ∫ t,(t-1)*f (Function.update x i t) ∂law
def conditionalDerivative {n : ℕ} (f : (Fin n→ℝ)→ℝ) (i : Fin n) (x : Fin n→ℝ) : ℝ :=
  ∫ t,coordinateDeriv f i (Function.update x i t) ∂law
def absoluteCenteredMoment : ℝ := ∫ t,‖t-1‖ ∂law

lemma conditionalCovariance_measurable {n : ℕ} (f : (Fin n→ℝ)→ℝ)
    (hf : StronglyMeasurable f) (i : Fin n) : StronglyMeasurable (conditionalCovariance f i) := by
  have hu : Measurable (fun p : (Fin n→ℝ)×ℝ => Function.update p.1 i p.2) := by fun_prop
  exact (((measurable_snd.sub_const 1).stronglyMeasurable).mul
    (hf.comp_measurable hu)).integral_prod_right'

lemma conditionalDerivative_measurable {n : ℕ} (f : (Fin n→ℝ)→ℝ) (i : Fin n)
    (hd : StronglyMeasurable (coordinateDeriv f i)) :
    StronglyMeasurable (conditionalDerivative f i) := by
  have hu : Measurable (fun p : (Fin n→ℝ)×ℝ => Function.update p.1 i p.2) := by fun_prop
  exact (hd.comp_measurable hu).integral_prod_right'

lemma conditionalCovariance_update {n : ℕ} (f : (Fin n→ℝ)→ℝ) (i : Fin n)
    (x : Fin n→ℝ) (t : ℝ) :
    conditionalCovariance f i (Function.update x i t)=conditionalCovariance f i x := by
  simp [conditionalCovariance,Function.update_idem]
lemma conditionalDerivative_update {n : ℕ} (f : (Fin n→ℝ)→ℝ) (i : Fin n)
    (x : Fin n→ℝ) (t : ℝ) :
    conditionalDerivative f i (Function.update x i t)=conditionalDerivative f i x := by
  simp [conditionalDerivative,Function.update_idem]

lemma conditionalCovariance_bound {n : ℕ} (f : (Fin n→ℝ)→ℝ)
    (hf : StronglyMeasurable f) {C : ℝ} (hb : ∀ x,‖f x‖≤C) (i : Fin n) (x : Fin n→ℝ) :
    ‖conditionalCovariance f i x‖≤absoluteCenteredMoment*C := by
  have hfp:MemLp (fun t=>f (Function.update x i t)) 2 law :=
    MemLp.of_bound (hf.comp_measurable (by fun_prop)).aestronglyMeasurable C
      (.of_forall fun t=>hb _)
  have hX:=expMeasure_one_memLp_centered
  have hp:=hX.integrable_mul hfp
  unfold conditionalCovariance
  calc
    ‖∫ t,(t-1)*f (Function.update x i t) ∂law‖≤
        ∫ t,‖(t-1)*f (Function.update x i t)‖ ∂law := norm_integral_le_integral_norm _
    _≤∫ t,‖t-1‖*C ∂law := by
      apply integral_mono hp.norm (hX.integrable (by norm_num) |>.norm.mul_const C)
      intro t
      change ‖(t-1)*f (Function.update x i t)‖≤‖t-1‖*C
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)
    _=absoluteCenteredMoment*C := by rw [integral_mul_const];rfl

lemma conditionalDerivative_bound {n : ℕ} (f : (Fin n→ℝ)→ℝ) {D : ℝ}
    (hdb : ∀ i x,‖coordinateDeriv f i x‖≤D) (i : Fin n) (x : Fin n→ℝ) :
    ‖conditionalDerivative f i x‖≤D := by
  simpa [conditionalDerivative] using
    (norm_integral_le_of_norm_le_const (μ:=law)
      (f:=fun t=>coordinateDeriv f i (Function.update x i t))
      (.of_forall fun t=>hdb i _))

lemma conditionalCovariance_integral {n : ℕ} (f : (Fin n→ℝ)→ℝ)
    (hf : StronglyMeasurable f) {C : ℝ} (hb : ∀ x,‖f x‖≤C) (i : Fin n) :
    (∫ x,conditionalCovariance f i x ∂productLaw n)=
      ∫ x,(x i-1)*f x ∂productLaw n := by
  have hfp:MemLp f 2 (productLaw n) := MemLp.of_bound hf.aestronglyMeasurable C (.of_forall hb)
  have hX:MemLp (fun x:Fin n→ℝ=>x i-1) 2 (productLaw n) :=
    expMeasure_one_memLp_centered.comp_measurePreserving
      (measurePreserving_eval (fun _:Fin n=>law) i)
  have hm:StronglyMeasurable (fun x:Fin n→ℝ=>(x i-1)*f x) :=
    ((measurable_pi_apply i).sub_const 1).stronglyMeasurable.mul hf
  simpa only [conditionalCovariance,Function.update_self] using
    integral_coordinate_resampling (fun x:Fin n→ℝ=>(x i-1)*f x) hm (hX.integrable_mul hfp) i

lemma conditionalDerivative_integral {n : ℕ} (f : (Fin n→ℝ)→ℝ)
    (hd : ∀ i,StronglyMeasurable (coordinateDeriv f i)) {D : ℝ}
    (hdb : ∀ i x,‖coordinateDeriv f i x‖≤D) (i : Fin n) :
    (∫ x,conditionalDerivative f i x ∂productLaw n)=
      ∫ x,coordinateDeriv f i x ∂productLaw n := by
  have hi:Integrable (coordinateDeriv f i) (productLaw n) :=
    (MemLp.of_bound (hd i).aestronglyMeasurable D (.of_forall (hdb i))
      : MemLp _ 2 (productLaw n)).integrable (by norm_num)
  exact integral_coordinate_resampling _ (hd i) hi i

/-- Full charged upper bound in every finite product dimension, with
ordinary coordinate derivatives and all actual conditional charges. -/
theorem exponential_finite_product_charged (n : ℕ) (f : (Fin n→ℝ)→ℝ)
    (hf : StronglyMeasurable f) {C D : ℝ} (hb : ∀ x,‖f x‖≤C)
    (hreg : ∀ i x,ContDiff ℝ 1 (fun t=>f (Function.update x i t)))
    (hc : ∀ i x,HasCompactSupport (fun t=>f (Function.update x i t)))
    (hd : ∀ i,StronglyMeasurable (coordinateDeriv f i))
    (hdb : ∀ i x,‖coordinateDeriv f i x‖≤D) :
    variance f (productLaw n)+
      (∑ i,((∫ x,(x i-1)*f x ∂productLaw n)-
        2*(∫ x,coordinateDeriv f i x ∂productLaw n))^2)+
      2*(∑ i,(∫ x,coordinateDeriv f i x ∂productLaw n)^2)≤
        4*(∫ x,∑ i,(coordinateDeriv f i x)^2 ∂productLaw n) := by
  let a:Fin n→(Fin n→ℝ)→ℝ:=fun i x=>conditionalCovariance f i x-2*conditionalDerivative f i x
  let b:Fin n→(Fin n→ℝ)→ℝ:=conditionalDerivative f
  have hm (i) := conditionalCovariance_measurable f hf i
  have hmB (i) := conditionalCovariance_bound f hf hb i
  have hd' (i) := conditionalDerivative_measurable f i (hd i)
  have hdB (i) := conditionalDerivative_bound f hdb i
  have he:=finite_product_charged_energy_bound n f hf hb
    (fun i x=>4*(coordinateDeriv f i x)^2) a b
    (fun i=>(hd i).pow 2 |>.const_mul 4)
    (D:=4*D^2) (fun i x=>by
      rw [Real.norm_of_nonneg (by positivity)]
      nlinarith [square_le_of_norm_le (hdb i x)])
    (fun i=>(hm i).sub ((hd' i).const_mul 2))
    (A:=absoluteCenteredMoment*C+2*D) (fun i x=>by
      dsimp [a]
      calc
        ‖conditionalCovariance f i x-2*conditionalDerivative f i x‖≤
          ‖conditionalCovariance f i x‖+‖2*conditionalDerivative f i x‖:=norm_sub_le _ _
        _≤absoluteCenteredMoment*C+2*D := by
          rw [norm_mul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)]
          linarith [hmB i x,hdB i x])
    hd' (B:=D) hdB
    (fun i x t=>by simp only [a,conditionalCovariance_update,conditionalDerivative_update])
    (fun i x t=>conditionalDerivative_update f i x t)
    (fun i x=>by
      simpa only [a,b,conditionalCovariance,conditionalDerivative,coordinateDeriv_update,
        integral_const_mul] using charged_core (fun t=>f (Function.update x i t)) (hreg i x) (hc i x))
  have hAi (i) : (∫ x,a i x ∂productLaw n)=
      (∫ x,(x i-1)*f x ∂productLaw n)-2*(∫ x,coordinateDeriv f i x ∂productLaw n) := by
    have hmi:Integrable (conditionalCovariance f i) (productLaw n) :=
      (MemLp.of_bound (hm i).aestronglyMeasurable (absoluteCenteredMoment*C) (.of_forall (hmB i))
        : MemLp _ 2 (productLaw n)).integrable (by norm_num)
    have hdi:Integrable (conditionalDerivative f i) (productLaw n) :=
      (MemLp.of_bound (hd' i).aestronglyMeasurable D (.of_forall (hdB i))
        : MemLp _ 2 (productLaw n)).integrable (by norm_num)
    dsimp [a]
    rw [integral_sub (f:=fun x=>conditionalCovariance f i x)
      (g:=fun x=>2*conditionalDerivative f i x) hmi (hdi.const_mul 2),integral_const_mul,
      conditionalCovariance_integral f hf hb i,conditionalDerivative_integral f hd hdb i]
  simpa only [hAi,b,conditionalDerivative_integral f hd hdb,←Finset.mul_sum,
    integral_const_mul] using he

end KLSImprovement.Tensorization
#print axioms KLSImprovement.Tensorization.conditionalCovariance_integral
#print axioms KLSImprovement.Tensorization.exponential_finite_product_charged

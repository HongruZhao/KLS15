import TwoConePolynomialMoments
import SingleSlotCounterexampleDensity

/-! Log-concavity of the actual parametric two-cone probability law.
It follows from its convex support and convex piecewise linear potential,
not from a general claim about mixtures. -/
noncomputable section
open MeasureTheory Set Matrix
open scoped BigOperators ENNReal
namespace KLSImprovement.TwoConeLogConcave
open KLS KLSImprovement.ProductAdmissible
open KLSImprovement.TwoConeMoments
open KLSImprovement.SingleSlotCounterexample
  (component polynomialMap actionDensity actionDensity_measurable map_raw_eq_density)
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def coneCoefficient (d g:ℝ):ℝ := (d+1)*g
def rightMatrix (d g:ℝ):Matrix (Fin 2) (Fin 2) ℝ :=
  !![1,coneCoefficient d g;0,-d]
theorem rightMatrix_det {d:ℝ} (hd:0 < d) (g:ℝ):(rightMatrix d g).det≠0 := by
  simpa [rightMatrix,Matrix.det_fin_two] using neg_ne_zero.mpr hd.ne'
def rightEquiv (d g:ℝ) (hd:0 < d):Space 2≃ᴬ[ℝ]Space 2 :=
  affineMatrixEquiv (rightMatrix d g) 0 (rightMatrix_det hd g)

theorem rightEquiv_apply (d g:ℝ) (hd:0 < d) (x:Space 2):
    rightEquiv d g hd x=WithLp.toLp 2 ![x 0+coneCoefficient d g*x 1,-d*x 1] := by
  ext i
  fin_cases i <;>simp [rightEquiv,affineMatrixEquiv_apply,affineMatrixMap_apply,
    matrixAction_apply,rightMatrix,Fin.sum_univ_two]

theorem rightEquiv_symm_apply (d g:ℝ) (hd:0 < d) (x:Space 2):
    (rightEquiv d g hd).symm x=
      WithLp.toLp 2 ![x 0+coneCoefficient d g/d*x 1,-x 1/d] := by
  apply (rightEquiv d g hd).injective
  rw [(rightEquiv d g hd).apply_symm_apply,rightEquiv_apply]
  ext i
  fin_cases i <;>simp <;>field_simp [hd.ne'] <;>ring

theorem component_left_eq:component leftPoly=rawEuclideanProduct 2 := by
  unfold component rawEuclideanProduct
  congr 1
  funext y
  ext i
  fin_cases i <;>simp [polynomialMap,leftPoly]

theorem component_right_eq_map (d g:ℝ) (hd:0 < d):
    component (rightPoly d g)=(rawEuclideanProduct 2).map (rightEquiv d g hd) := by
  rw [component,rawEuclideanProduct,
    Measure.map_map (rightEquiv d g hd).continuous.measurable
      (MeasurableEquiv.toLp 2 (Fin 2→ℝ)).measurable]
  congr 1
  funext y
  rw [Function.comp_apply,rightEquiv_apply]
  ext i
  fin_cases i
  · change MvPolynomial.eval y (MvPolynomial.X 0+
      MvPolynomial.C ((d+1)*g)*MvPolynomial.X 1)=y 0+coneCoefficient d g*y 1
    simp only [MvPolynomial.eval_add,MvPolynomial.eval_mul,MvPolynomial.eval_C,
      MvPolynomial.eval_X,coneCoefficient]
  · change MvPolynomial.eval y (MvPolynomial.C (-d)*MvPolynomial.X 1)=-d*y 1
    simp only [MvPolynomial.eval_mul,MvPolynomial.eval_C,MvPolynomial.eval_X]

theorem right_density_formula (d g:ℝ) (hd:0 < d) (x:Space 2):
    actionDensity (rightMatrix d g) (rightMatrix_det hd g) x=
      if 0≤d*x 0+coneCoefficient d g*x 1 ∧ x 1≤0 then
        ENNReal.ofReal d⁻¹*ENNReal.ofReal
          (Real.exp (-(x 0+(coneCoefficient d g-1)/d*x 1))) else 0 := by
  have hdet : |(rightMatrix d g).det⁻¹|=d⁻¹ := by
    simp [rightMatrix,Matrix.det_fin_two,abs_inv,abs_of_pos hd]
  unfold actionDensity
  rw [hdet]
  change ENNReal.ofReal d⁻¹*rawDensity 2 ((rightEquiv d g hd).symm x)=_
  rw [rawDensity_formula,rightEquiv_symm_apply]
  simp only [PiLp.toLp_apply,Fin.forall_fin_two,Fin.sum_univ_two,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  have he : d*(x 0+coneCoefficient d g/d*x 1)=
      d*x 0+coneCoefficient d g*x 1 := by field_simp [hd.ne'] <;>ring
  have hc : (0≤x 0+coneCoefficient d g/d*x 1 ∧ 0≤-x 1/d) ↔
      (0≤d*x 0+coneCoefficient d g*x 1 ∧ x 1≤0) := by
    constructor
    · rintro ⟨h0,h1⟩
      constructor
      · rw [←he]
        exact mul_nonneg hd.le h0
      · have ht := (le_div_iff₀ hd).mp h1
        linarith
    · rintro ⟨h0,h1⟩
      constructor
      · rw [←he] at h0
        exact nonneg_of_mul_nonneg_right h0 hd
      · exact div_nonneg (neg_nonneg.mpr h1) hd.le
  simp only [hc]
  have hex : -(x 0+coneCoefficient d g/d*x 1+-x 1/d)=
      -(x 0+(coneCoefficient d g-1)/d*x 1) := by ring
  rw [hex]
  split_ifs <;>simp

def potential (d g:ℝ) (x:Space 2):ℝ :=
  max (x 0+x 1) (x 0+(coneCoefficient d g-1)/d*x 1)+Real.log (d+1)
def density (d g:ℝ) (x:Space 2):ℝ≥0∞ :=
  if 0≤x 0 ∧ 0≤d*x 0+coneCoefficient d g*x 1 then
    ENNReal.ofReal (Real.exp (-potential d g x)) else 0

@[fun_prop] theorem density_measurable (d g:ℝ):Measurable (density d g) := by
  have he : density d g=({x:Space 2 | 0≤x 0 ∧ 0≤d*x 0+coneCoefficient d g*x 1}.indicator
      (fun x=>ENNReal.ofReal (Real.exp (-potential d g x)))) := by
    funext x
    by_cases hx:0≤x 0 ∧ 0≤d*x 0+coneCoefficient d g*x 1 <;>
      simp only [density,Set.indicator,Set.mem_ofPred_eq,hx,ite_true,ite_false]
  rw [he]
  apply Measurable.indicator
  · unfold potential
    fun_prop
  · have h0:MeasurableSet {x:Space 2 | 0≤x 0} :=
      measurableSet_le measurable_const (by fun_prop)
    have h1:MeasurableSet {x:Space 2 | 0≤d*x 0+coneCoefficient d g*x 1} :=
      measurableSet_le measurable_const (by fun_prop)
    exact h0.inter h1

theorem density_scaled (d g:ℝ) (hd:0 < d) (x:Space 2):density d g x=
    if 0≤x 0 ∧ 0≤d*x 0+coneCoefficient d g*x 1 then
      ENNReal.ofReal (1/(d+1))*ENNReal.ofReal
        (Real.exp (-max (x 0+x 1) (x 0+(coneCoefficient d g-1)/d*x 1))) else 0 := by
  have hden : 0 < d+1 := by linarith
  have he : Real.exp (-potential d g x)=1/(d+1)*
      Real.exp (-max (x 0+x 1) (x 0+(coneCoefficient d g-1)/d*x 1)) := by
    simp only [potential,neg_add,Real.exp_add,Real.exp_neg,Real.exp_log hden]
    ring
  unfold density
  rw [he,ENNReal.ofReal_mul (div_nonneg zero_le_one hden.le)]

def boundaryForm :Space 2→ₗ[ℝ]ℝ :=
  { toFun:=fun x=>x 1
    map_add':=by intro x y;rfl
    map_smul':=by intro c x;rfl }
theorem ae_off_boundary :∀ᵐ x:Space 2∂volume,x 1≠0 := by
  have hk : LinearMap.ker boundaryForm≠⊤ := by
    intro h
    have hm:(WithLp.toLp 2 ![0,1]:Space 2)∈LinearMap.ker boundaryForm := by rw [h];trivial
    change (1:ℝ)=0 at hm
    norm_num at hm
  have hz := Measure.addHaar_submodule (volume:Measure (Space 2)) (LinearMap.ker boundaryForm) hk
  filter_upwards [compl_mem_ae_iff.mpr hz] with x hx
  exact hx

theorem mixture_density_eq {d g:ℝ} (hd:0 < d) (hg:0≤g) (hg1:g≤1)
    (x:Space 2) (hx:x 1≠0):
    ENNReal.ofReal (1/(d+1))*rawDensity 2 x+
      ENNReal.ofReal (d/(d+1))*actionDensity (rightMatrix d g) (rightMatrix_det hd g) x=
        density d g x := by
  have hden : 0 < d+1 := by linarith
  have hc : 0≤coneCoefficient d g := mul_nonneg hden.le hg
  have hc1 : coneCoefficient d g≤d+1 := by
    exact (mul_le_mul_of_nonneg_left hg1 hden.le).trans_eq (mul_one _)
  have hs : (coneCoefficient d g-1)/d≤1 := (div_le_one hd).mpr (by linarith)
  rw [right_density_formula d g hd,density_scaled d g hd,rawDensity_formula]
  simp only [Fin.forall_fin_two,Fin.sum_univ_two]
  rcases lt_or_gt_of_ne hx with hneg|hpos
  · have hL : ¬(0≤x 0 ∧ 0≤x 1) := by rintro ⟨_,h⟩;linarith
    have hm : x 0+x 1≤x 0+(coneCoefficient d g-1)/d*x 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hs) (neg_nonneg.mpr hneg.le)]
    rw [ite_eq_right hL,max_eq_right hm]
    by_cases hR:0≤d*x 0+coneCoefficient d g*x 1
    · have h0 : 0≤x 0 := by
        have ht : coneCoefficient d g*x 1≤0 := mul_nonpos_of_nonneg_of_nonpos hc hneg.le
        nlinarith
      rw [ite_eq_left ⟨hR,hneg.le⟩,ite_eq_left ⟨h0,hR⟩]
      simp only [mul_zero,zero_add]
      rw [←mul_assoc,←ENNReal.ofReal_mul (div_nonneg hd.le hden.le)]
      have hw : d/(d+1)*d⁻¹=1/(d+1) := by field_simp [hd.ne',hden.ne'] <;>ring
      rw [hw]
    · have hR' : ¬(0≤d*x 0+coneCoefficient d g*x 1 ∧ x 1≤0) := by tauto
      have hS : ¬(0≤x 0 ∧ 0≤d*x 0+coneCoefficient d g*x 1) := by tauto
      simp only [hR',hS,ite_false,mul_zero,add_zero]
  · have hR : ¬(0≤d*x 0+coneCoefficient d g*x 1 ∧ x 1≤0) := by rintro ⟨_,h⟩;linarith
    have hm : x 0+(coneCoefficient d g-1)/d*x 1≤x 0+x 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hs) hpos.le]
    rw [ite_eq_right hR,max_eq_left hm]
    simp only [mul_zero,add_zero]
    by_cases h0:0≤x 0
    · have hS : 0≤d*x 0+coneCoefficient d g*x 1 :=
        add_nonneg (mul_nonneg hd.le h0) (mul_nonneg hc hpos.le)
      rw [ite_eq_left ⟨h0,hpos.le⟩,ite_eq_left ⟨h0,hS⟩]
    · have hL : ¬(0≤x 0 ∧ 0≤x 1) := by tauto
      have hS : ¬(0≤x 0 ∧ 0≤d*x 0+coneCoefficient d g*x 1) := by tauto
      simp only [hL,hS,ite_false,mul_zero]

theorem rawMeasure_eq_density {d g:ℝ} (hd:0 < d) (hg:0≤g) (hg1:g≤1):
    rawMeasure d g=volume.withDensity (density d g) := by
  rw [rawMeasure,component_left_eq,component_right_eq_map d g hd,rightEquiv,
    map_raw_eq_density,rawEuclideanProduct_eq_density,
    ←withDensity_smul _ (by unfold rawDensity;fun_prop),
    ←withDensity_smul _ (actionDensity_measurable _ _),
    ←withDensity_add_left (by unfold rawDensity;fun_prop)]
  apply withDensity_congr_ae
  filter_upwards [ae_off_boundary] with x hx
  exact mixture_density_eq hd hg hg1 x hx

theorem potential_convex_combination (d g:ℝ) (x y:Space 2) (t:ℝ)
    (ht0:0≤t) (ht1:t≤1):
    potential d g (t • x+(1-t) • y)≤t*potential d g x+(1-t)*potential d g y := by
  let k:ℝ := (coneCoefficient d g-1)/d
  have hL : t*(x 0+x 1)+(1-t)*(y 0+y 1)≤
      t*max (x 0+x 1) (x 0+k*x 1)+(1-t)*max (y 0+y 1) (y 0+k*y 1) :=
    add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ht0)
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr ht1))
  have hR : t*(x 0+k*x 1)+(1-t)*(y 0+k*y 1)≤
      t*max (x 0+x 1) (x 0+k*x 1)+(1-t)*max (y 0+y 1) (y 0+k*y 1) :=
    add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) ht0)
      (mul_le_mul_of_nonneg_left (le_max_right _ _) (sub_nonneg.mpr ht1))
  calc
    potential d g (t • x+(1-t) • y)=
        max (t*(x 0+x 1)+(1-t)*(y 0+y 1))
          (t*(x 0+k*x 1)+(1-t)*(y 0+k*y 1))+Real.log (d+1) := by
      unfold potential
      congr 1
      apply congrArg₂ max <;>
        simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,k] <;>ring
    _ ≤ t*max (x 0+x 1) (x 0+k*x 1)+
        (1-t)*max (y 0+y 1) (y 0+k*y 1)+Real.log (d+1) :=
      add_le_add (max_le hL hR) le_rfl
    _ = t*potential d g x+(1-t)*potential d g y := by unfold potential;dsimp only [k];ring

theorem density_pointwise_logConcave (d g:ℝ) (x y:Space 2) (t:ℝ)
    (ht0:0 < t) (ht1:t<1):
    density d g x^t*density d g y^(1-t)≤density d g (t • x+(1-t) • y) := by
  unfold density
  by_cases hx:0≤x 0 ∧ 0≤d*x 0+coneCoefficient d g*x 1
  · by_cases hy:0≤y 0 ∧ 0≤d*y 0+coneCoefficient d g*y 1
    · have hz : 0≤(t • x+(1-t) • y) 0 ∧
          0≤d*(t • x+(1-t) • y) 0+coneCoefficient d g*(t • x+(1-t) • y) 1 := by
        constructor
        · change 0≤t*x 0+(1-t)*y 0
          exact add_nonneg (mul_nonneg ht0.le hx.1) (mul_nonneg (sub_pos.mpr ht1).le hy.1)
        · have he : d*(t • x+(1-t) • y) 0+coneCoefficient d g*(t • x+(1-t) • y) 1=
              t*(d*x 0+coneCoefficient d g*x 1)+(1-t)*(d*y 0+coneCoefficient d g*y 1) := by
            simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
            ring
          rw [he]
          exact add_nonneg (mul_nonneg ht0.le hx.2) (mul_nonneg (sub_pos.mpr ht1).le hy.2)
      rw [ite_eq_left hx,ite_eq_left hy,ite_eq_left hz,
        ←exp_neg_affine_eq_geometric (potential d g x) (potential d g y) t (1-t)
          ht0.le (sub_pos.mpr ht1).le]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg
        (potential_convex_combination d g x y t ht0.le ht1.le)))
    · simp only [hy,ite_false,ENNReal.zero_rpow_of_pos (sub_pos.mpr ht1),mul_zero]
      exact zero_le
  · simp only [hx,ite_false,ENNReal.zero_rpow_of_pos ht0,zero_mul]
    exact zero_le

theorem raw_logConcave {d g:ℝ} (hd:0 < d) (hg:0≤g) (hg1:g≤1):
    measureLogConcave (rawMeasure d g) := by
  rw [rawMeasure_eq_density hd hg hg1]
  exact measureLogConcave_withDensity_of_pointwise (density_measurable d g)
    (density_pointwise_logConcave d g)

end KLSImprovement.TwoConeLogConcave
#print axioms KLSImprovement.TwoConeLogConcave.rawMeasure_eq_density
#print axioms KLSImprovement.TwoConeLogConcave.raw_logConcave

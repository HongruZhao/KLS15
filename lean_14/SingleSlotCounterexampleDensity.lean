import SingleSlotCounterexampleMoments
import ActualProductAdmissible
import KLS.AffinePotentialCutoff

/-! Density identification for the actual two-cone mixture. Its log-concavity
will follow from a convex piecewise linear potential, rather than from a
general assertion about mixtures. -/
noncomputable section
open MeasureTheory Set Matrix
open scoped BigOperators ENNReal
namespace KLSImprovement.SingleSlotCounterexample
open KLS KLSImprovement.ProductAdmissible
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def leftMatrix :Matrix (Fin 2) (Fin 2) ℝ := !![4/5,0;1/5,1]
def rightMatrix :Matrix (Fin 2) (Fin 2) ℝ := !![4/5,1/6;1/5,0]
theorem leftMatrix_det :leftMatrix.det≠0 := by norm_num [leftMatrix,Matrix.det_fin_two]
theorem rightMatrix_det :rightMatrix.det≠0 := by norm_num [rightMatrix,Matrix.det_fin_two]
def leftEquiv :Space 2≃ᴬ[ℝ]Space 2 := affineMatrixEquiv leftMatrix 0 leftMatrix_det
def rightEquiv :Space 2≃ᴬ[ℝ]Space 2 := affineMatrixEquiv rightMatrix 0 rightMatrix_det

theorem leftEquiv_apply (x:Space 2):
    leftEquiv x=WithLp.toLp 2 ![(4/5:ℝ)*x 0,(1/5:ℝ)*x 0+x 1] := by
  ext i
  fin_cases i <;>simp [leftEquiv,affineMatrixEquiv_apply,affineMatrixMap_apply,
    matrixAction_apply,leftMatrix,Fin.sum_univ_two]

theorem rightEquiv_apply (x:Space 2):
    rightEquiv x=WithLp.toLp 2 ![(4/5:ℝ)*x 0+(1/6:ℝ)*x 1,(1/5:ℝ)*x 0] := by
  ext i
  fin_cases i <;>simp [rightEquiv,affineMatrixEquiv_apply,affineMatrixMap_apply,
    matrixAction_apply,rightMatrix,Fin.sum_univ_two]

theorem leftEquiv_symm_apply (x:Space 2):
    leftEquiv.symm x=WithLp.toLp 2 ![(5/4:ℝ)*x 0,x 1-x 0/4] := by
  apply leftEquiv.injective
  rw [leftEquiv.apply_symm_apply,leftEquiv_apply]
  ext i
  fin_cases i <;>simp <;>ring

theorem rightEquiv_symm_apply (x:Space 2):
    rightEquiv.symm x=WithLp.toLp 2 ![5*x 1,6*x 0-24*x 1] := by
  apply rightEquiv.injective
  rw [rightEquiv.apply_symm_apply,rightEquiv_apply]
  ext i
  fin_cases i <;>simp <;>ring

theorem component_left_eq_map :component leftPoly=
    (rawEuclideanProduct 2).map leftEquiv := by
  rw [component,rawEuclideanProduct,Measure.map_map leftEquiv.continuous.measurable
    (MeasurableEquiv.toLp 2 (Fin 2→ℝ)).measurable]
  congr 1
  funext y
  rw [Function.comp_apply,leftEquiv_apply]
  ext i
  fin_cases i
  · change MvPolynomial.eval y (MvPolynomial.C (4/5:ℝ)*MvPolynomial.X 0)=(4/5:ℝ)*y 0
    simp only [MvPolynomial.eval_mul,MvPolynomial.eval_C,MvPolynomial.eval_X]
  · change MvPolynomial.eval y (MvPolynomial.C (1/5:ℝ)*MvPolynomial.X 0+MvPolynomial.X 1)=
      (1/5:ℝ)*y 0+y 1
    simp only [MvPolynomial.eval_add,MvPolynomial.eval_mul,MvPolynomial.eval_C,MvPolynomial.eval_X]

theorem component_right_eq_map :component rightPoly=
    (rawEuclideanProduct 2).map rightEquiv := by
  rw [component,rawEuclideanProduct,Measure.map_map rightEquiv.continuous.measurable
    (MeasurableEquiv.toLp 2 (Fin 2→ℝ)).measurable]
  congr 1
  funext y
  rw [Function.comp_apply,rightEquiv_apply]
  ext i
  fin_cases i
  · change MvPolynomial.eval y (MvPolynomial.C (4/5:ℝ)*MvPolynomial.X 0+
      MvPolynomial.C (1/6:ℝ)*MvPolynomial.X 1)=(4/5:ℝ)*y 0+(1/6:ℝ)*y 1
    simp only [MvPolynomial.eval_add,MvPolynomial.eval_mul,MvPolynomial.eval_C,MvPolynomial.eval_X]
  · change MvPolynomial.eval y (MvPolynomial.C (1/5:ℝ)*MvPolynomial.X 0)=(1/5:ℝ)*y 0
    simp only [MvPolynomial.eval_mul,MvPolynomial.eval_C,MvPolynomial.eval_X]

def actionDensity (A:Matrix (Fin 2) (Fin 2) ℝ) (hA:A.det≠0) (x:Space 2):ℝ≥0∞ :=
  ENNReal.ofReal |A.det⁻¹| * rawDensity 2 ((affineMatrixEquiv A 0 hA).symm x)

@[fun_prop] theorem actionDensity_measurable (A:Matrix (Fin 2) (Fin 2) ℝ) (hA:A.det≠0):
    Measurable (actionDensity A hA) := by
  unfold actionDensity rawDensity
  fun_prop

theorem map_raw_eq_density (A:Matrix (Fin 2) (Fin 2) ℝ) (hA:A.det≠0):
    (rawEuclideanProduct 2).map (affineMatrixEquiv A 0 hA)=
      volume.withDensity (actionDensity A hA) := by
  let e:Space 2≃ᵐSpace 2 := (affineMatrixEquiv A 0 hA).toHomeomorph.toMeasurableEquiv
  rw [rawEuclideanProduct_eq_density]
  change (volume.withDensity (rawDensity 2)).map e=_
  rw [map_withDensity_measurableEquiv e _ _ (by unfold rawDensity;fun_prop)]
  change ((volume.map (affineMatrixEquiv A 0 hA)).withDensity _)=_
  rw [map_volume_affineMatrixEquiv,withDensity_smul_measure,
    ←withDensity_smul _ (by unfold rawDensity;fun_prop)]
  rfl

theorem left_density_formula (x:Space 2):actionDensity leftMatrix leftMatrix_det x=
    if 0≤x 0 ∧ x 0≤4*x 1 then
      ENNReal.ofReal (5/4:ℝ)*ENNReal.ofReal (Real.exp (-(x 0+x 1))) else 0 := by
  have hd:ENNReal.ofReal |leftMatrix.det⁻¹|=ENNReal.ofReal (5/4:ℝ) := by
    norm_num [leftMatrix,Matrix.det_fin_two]
  unfold actionDensity
  rw [hd]
  change ENNReal.ofReal (5/4:ℝ)*rawDensity 2 (leftEquiv.symm x)=_
  rw [rawDensity_formula,leftEquiv_symm_apply]
  simp only [PiLp.toLp_apply,Fin.forall_fin_two,Fin.sum_univ_two,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  have hc:(0≤(5/4:ℝ)*x 0 ∧ 0≤x 1-x 0/4) ↔ (0≤x 0 ∧ x 0≤4*x 1) := by
    constructor <;>rintro ⟨h0,h1⟩ <;>constructor <;>linarith
  simp only [hc]
  have he: -((5/4:ℝ)*x 0+(x 1-x 0/4))=-(x 0+x 1) := by ring
  rw [he]
  split_ifs <;>simp

theorem right_density_formula (x:Space 2):actionDensity rightMatrix rightMatrix_det x=
    if 0≤x 1 ∧ 4*x 1≤x 0 then
      ENNReal.ofReal (30:ℝ)*ENNReal.ofReal (Real.exp (-(6*x 0-19*x 1))) else 0 := by
  have hd:ENNReal.ofReal |rightMatrix.det⁻¹|=ENNReal.ofReal (30:ℝ) := by
    norm_num [rightMatrix,Matrix.det_fin_two]
  unfold actionDensity
  rw [hd]
  change ENNReal.ofReal (30:ℝ)*rawDensity 2 (rightEquiv.symm x)=_
  rw [rawDensity_formula,rightEquiv_symm_apply]
  simp only [PiLp.toLp_apply,Fin.forall_fin_two,Fin.sum_univ_two,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  have hc:(0≤5*x 1 ∧ 0≤6*x 0-24*x 1) ↔ (0≤x 1 ∧ 4*x 1≤x 0) := by
    constructor <;>rintro ⟨h0,h1⟩ <;>constructor <;>linarith
  simp only [hc]
  have he: -(5*x 1+(6*x 0-24*x 1))=-(6*x 0-19*x 1) := by ring
  rw [he]
  split_ifs <;>simp

def potential (x:Space 2):ℝ :=
  max (x 0+x 1) (6*x 0-19*x 1)-Real.log (6/5:ℝ)
def density (x:Space 2):ℝ≥0∞ :=
  if 0≤x 0 ∧ 0≤x 1 then ENNReal.ofReal (Real.exp (-potential x)) else 0

@[fun_prop] theorem density_measurable :Measurable density := by
  have he:density=({x:Space 2|0≤x 0 ∧ 0≤x 1}.indicator
      (fun x=>ENNReal.ofReal (Real.exp (-potential x)))) := by
    funext x
    by_cases hx:0≤x 0 ∧ 0≤x 1 <;>
      simp only [density,Set.indicator,Set.mem_ofPred_eq,hx,ite_true,ite_false]
  rw [he]
  apply Measurable.indicator
  · unfold potential
    fun_prop
  · have h0:MeasurableSet {x:Space 2|0≤x 0} :=
      measurableSet_le measurable_const (by fun_prop)
    have h1:MeasurableSet {x:Space 2|0≤x 1} :=
      measurableSet_le measurable_const (by fun_prop)
    exact h0.inter h1

theorem density_scaled (x:Space 2):density x=
    if 0≤x 0 ∧ 0≤x 1 then ENNReal.ofReal (6/5:ℝ)*
      ENNReal.ofReal (Real.exp (-max (x 0+x 1) (6*x 0-19*x 1))) else 0 := by
  unfold density potential
  split_ifs
  · rw [neg_sub,Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<6/5),
      div_eq_mul_inv,←Real.exp_neg,ENNReal.ofReal_mul (by norm_num)]
  · rfl

def boundaryForm :Space 2→ₗ[ℝ]ℝ :=
  { toFun:=fun x=>x 0-4*x 1
    map_add':=by intro x y;change (x 0+y 0)-4*(x 1+y 1)=_;ring
    map_smul':=by intro c x;change c*x 0-4*(c*x 1)=c*(x 0-4*x 1);ring }

theorem boundaryForm_kernel_ne_top :LinearMap.ker boundaryForm≠⊤ := by
  intro hk
  have hm:(WithLp.toLp 2 ![1,0]:Space 2)∈LinearMap.ker boundaryForm := by
    rw [hk]
    trivial
  change (1:ℝ)-4*0=0 at hm
  norm_num at hm

theorem ae_off_boundary :∀ᵐ x:Space 2∂volume,x 0≠4*x 1 := by
  have hz := Measure.addHaar_submodule (volume:Measure (Space 2))
    (LinearMap.ker boundaryForm) boundaryForm_kernel_ne_top
  filter_upwards [compl_mem_ae_iff.mpr hz] with x hx
  change ¬(x 0-4*x 1=0) at hx
  exact fun h=>hx (sub_eq_zero.mpr h)

theorem mixture_density_eq (x:Space 2) (hx:x 0≠4*x 1):
    ENNReal.ofReal (24/25:ℝ)*actionDensity leftMatrix leftMatrix_det x+
      ENNReal.ofReal (1/25:ℝ)*actionDensity rightMatrix rightMatrix_det x=density x := by
  rw [left_density_formula,right_density_formula,density_scaled]
  by_cases h0:0≤x 0
  · by_cases h1:0≤x 1
    · rcases lt_or_gt_of_ne hx with hlt|hgt
      · have hL:0≤x 0 ∧ x 0≤4*x 1 := ⟨h0,hlt.le⟩
        have hR:¬(0≤x 1 ∧ 4*x 1≤x 0) := by rintro ⟨_,h⟩;linarith
        have hm:6*x 0-19*x 1≤x 0+x 1 := by linarith
        rw [ite_eq_left hL,ite_eq_right hR,ite_eq_left ⟨h0,h1⟩,max_eq_left hm]
        simp only [mul_zero,add_zero]
        rw [←mul_assoc,←ENNReal.ofReal_mul (by norm_num)]
        norm_num
      · have hL:¬(0≤x 0 ∧ x 0≤4*x 1) := by rintro ⟨_,h⟩;linarith
        have hR:0≤x 1 ∧ 4*x 1≤x 0 := ⟨h1,hgt.le⟩
        have hm:x 0+x 1≤6*x 0-19*x 1 := by linarith
        rw [ite_eq_right hL,ite_eq_left hR,ite_eq_left ⟨h0,h1⟩,max_eq_right hm]
        simp only [mul_zero,zero_add]
        rw [←mul_assoc,←ENNReal.ofReal_mul (by norm_num)]
        norm_num
    · have hL:¬(0≤x 0 ∧ x 0≤4*x 1) := by rintro ⟨_,h⟩;linarith
      simp [hL,h1]
  · have hR:¬(0≤x 1 ∧ 4*x 1≤x 0) := by rintro ⟨h,h'⟩;linarith
    simp [h0,hR]

theorem rawMeasure_eq_density :rawMeasure=volume.withDensity density := by
  rw [rawMeasure,component_left_eq_map,component_right_eq_map,
    leftEquiv,rightEquiv,map_raw_eq_density,map_raw_eq_density,
    ←withDensity_smul _ (actionDensity_measurable _ _),
    ←withDensity_smul _ (actionDensity_measurable _ _),
    ←withDensity_add_left (by fun_prop)]
  apply withDensity_congr_ae
  filter_upwards [ae_off_boundary] with x hx
  exact mixture_density_eq x hx

end KLSImprovement.SingleSlotCounterexample
#print axioms KLSImprovement.SingleSlotCounterexample.rawMeasure_eq_density

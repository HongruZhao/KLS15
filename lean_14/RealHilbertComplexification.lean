import Mathlib

/-! The concrete complex Hilbert space of pairs from a real Hilbert space.
Its norm and operator extension will be used to bridge the genuine real
weighted primitive maps to the complex spectral endgame. -/
noncomputable section
namespace KLSBelow25
open InnerProductSpace
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

@[ext] structure RealHilbertComplexification (H : Type*) where
  re : H
  im : H

namespace RealHilbertComplexification
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def pairEquiv : RealHilbertComplexification H ≃ H × H where
  toFun x := (x.re,x.im)
  invFun x := ⟨x.1,x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (RealHilbertComplexification H) := pairEquiv.addCommGroup

@[simp] theorem zero_re : (0 : RealHilbertComplexification H).re = 0 := rfl
@[simp] theorem zero_im : (0 : RealHilbertComplexification H).im = 0 := rfl
@[simp] theorem add_re (x y : RealHilbertComplexification H) : (x+y).re=x.re+y.re := rfl
@[simp] theorem add_im (x y : RealHilbertComplexification H) : (x+y).im=x.im+y.im := rfl
@[simp] theorem neg_re (x : RealHilbertComplexification H) : (-x).re= -x.re := rfl
@[simp] theorem neg_im (x : RealHilbertComplexification H) : (-x).im= -x.im := rfl
@[simp] theorem sub_re (x y : RealHilbertComplexification H) : (x-y).re=x.re-y.re := rfl
@[simp] theorem sub_im (x y : RealHilbertComplexification H) : (x-y).im=x.im-y.im := rfl

instance : SMul ℂ (RealHilbertComplexification H) :=
  ⟨fun z x => ⟨z.re • x.re-z.im • x.im,z.im • x.re+z.re • x.im⟩⟩

@[simp] theorem smul_re (z : ℂ) (x : RealHilbertComplexification H) :
    (z • x).re=z.re • x.re-z.im • x.im := rfl
@[simp] theorem smul_im (z : ℂ) (x : RealHilbertComplexification H) :
    (z • x).im=z.im • x.re+z.re • x.im := rfl

instance : Module ℂ (RealHilbertComplexification H) where
  one_smul x := by ext <;> simp
  mul_smul z w x := by
    ext <;> simp [Complex.mul_re,Complex.mul_im,add_smul,sub_smul,
      mul_smul,smul_add,smul_sub] <;> module
  smul_zero z := by ext <;> simp
  smul_add z x y := by ext <;> simp [smul_add] <;> abel
  add_smul z w x := by ext <;> simp [add_smul] <;> abel
  zero_smul x := by ext <;> simp

def complexInner (x y : RealHilbertComplexification H) : ℂ :=
  ⟨⟪x.re,y.re⟫_ℝ+⟪x.im,y.im⟫_ℝ,⟪x.re,y.im⟫_ℝ-⟪x.im,y.re⟫_ℝ⟩

instance complexCore : InnerProductSpace.Core ℂ (RealHilbertComplexification H) where
  inner := complexInner
  conj_inner_symm x y := by
    apply Complex.ext <;> simp only [complexInner,Complex.conj_re,Complex.conj_im]
    · rw [real_inner_comm y.re x.re,real_inner_comm y.im x.im]
    · rw [real_inner_comm y.re x.im,real_inner_comm y.im x.re]; ring
  re_inner_nonneg x := by
    change 0 ≤ ⟪x.re,x.re⟫_ℝ+⟪x.im,x.im⟫_ℝ
    rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
    positivity
  add_left x y z := by
    apply Complex.ext <;> simp [complexInner,inner_add_left] <;> ring
  smul_left x y z := by
    apply Complex.ext <;> simp [complexInner,inner_sub_left,inner_add_left,
      real_inner_smul_left,Complex.mul_re,Complex.mul_im] <;> ring
  definite x hx := by
    have hre := congrArg Complex.re hx
    change ⟪x.re,x.re⟫_ℝ+⟪x.im,x.im⟫_ℝ=0 at hre
    rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hre
    have hr : x.re=0 := norm_eq_zero.mp (by nlinarith [norm_nonneg x.re,sq_nonneg ‖x.im‖])
    have hi : x.im=0 := norm_eq_zero.mp (by nlinarith [norm_nonneg x.im,sq_nonneg ‖x.re‖])
    ext <;> assumption

instance : NormedAddCommGroup (RealHilbertComplexification H) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
instance : InnerProductSpace ℂ (RealHilbertComplexification H) :=
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (RealHilbertComplexification H))

@[simp] theorem inner_re (x y : RealHilbertComplexification H) :
    Complex.re ⟪x,y⟫_ℂ = ⟪x.re,y.re⟫_ℝ+⟪x.im,y.im⟫_ℝ := rfl
@[simp] theorem inner_im (x y : RealHilbertComplexification H) :
    Complex.im ⟪x,y⟫_ℂ = ⟪x.re,y.im⟫_ℝ-⟪x.im,y.re⟫_ℝ := rfl

theorem norm_sq (x : RealHilbertComplexification H) : ‖x‖^2=‖x.re‖^2+‖x.im‖^2 := by
  rw [norm_sq_eq_re_inner (𝕜:=ℂ)]
  change ⟪x.re,x.re⟫_ℝ+⟪x.im,x.im⟫_ℝ=‖x.re‖^2+‖x.im‖^2
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]

def realLinearIsometryEquiv : RealHilbertComplexification H ≃ₗᵢ[ℝ] WithLp 2 (H × H) where
  toFun x := WithLp.toLp 2 (x.re,x.im)
  invFun x := ⟨(WithLp.ofLp x).1,(WithLp.ofLp x).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    apply WithLp.ofLp_injective 2
    change ((c • x).re,(c • x).im) = (c • x.re,c • x.im)
    apply Prod.ext <;> simp [← Complex.coe_smul]
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2,norm_sq]
    rfl

instance [CompleteSpace H] : CompleteSpace (RealHilbertComplexification H) :=
  realLinearIsometryEquiv.toIsometryEquiv.completeSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def extendLinear (T : H →L[ℝ] F) :
    RealHilbertComplexification H →ₗ[ℂ] RealHilbertComplexification F where
  toFun x := ⟨T x.re,T x.im⟩
  map_add' x y := by ext <;> simp
  map_smul' z x := by ext <;> simp

theorem extendLinear_bound (T : H →L[ℝ] F) (x : RealHilbertComplexification H) :
    ‖extendLinear T x‖ ≤ ‖T‖ * ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [norm_sq,mul_pow,norm_sq]
  change ‖T x.re‖^2+‖T x.im‖^2 ≤ ‖T‖^2*(‖x.re‖^2+‖x.im‖^2)
  have hr := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (T.le_opNorm x.re)
  have hi := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (T.le_opNorm x.im)
  nlinarith

def extend (T : H →L[ℝ] F) :
    RealHilbertComplexification H →L[ℂ] RealHilbertComplexification F :=
  (extendLinear T).mkContinuous ‖T‖ (extendLinear_bound T)

@[simp] theorem extend_re (T : H →L[ℝ] F) (x : RealHilbertComplexification H) :
    (extend T x).re=T x.re := rfl
@[simp] theorem extend_im (T : H →L[ℝ] F) (x : RealHilbertComplexification H) :
    (extend T x).im=T x.im := rfl

@[simp] theorem norm_real (x : H) : ‖(⟨x,0⟩ : RealHilbertComplexification H)‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [norm_sq]

@[simp] theorem norm_extend (T : H →L[ℝ] F) : ‖extend T‖=‖T‖ := by
  apply le_antisymm
  · exact (extend T).opNorm_le_bound (norm_nonneg _) (extendLinear_bound T)
  · apply T.opNorm_le_bound (norm_nonneg _)
    intro x
    have h := (extend T).le_opNorm (⟨x,0⟩ : RealHilbertComplexification H)
    have he : extend T (⟨x,0⟩ : RealHilbertComplexification H)=⟨T x,0⟩ := by ext <;> simp
    rw [he,norm_real,norm_real] at h
    exact h

#print axioms norm_sq
#print axioms realLinearIsometryEquiv
#print axioms norm_extend
end RealHilbertComplexification
end KLSBelow25

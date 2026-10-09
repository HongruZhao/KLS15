import Mathlib

/-! Actual bounded diagonal and backward-shift maps on Hilbert direct sums.
All rank bounds are assumed explicitly here; the maps are constructed on
the genuine square-summable families and their adjoints are identified. -/
noncomputable section
namespace KLSBelow25
namespace GradedHilbert
open ContinuousLinearMap InnerProductSpace
open scoped ENNReal
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {G E : ℕ → Type*}
  [∀ r, NormedAddCommGroup (G r)] [∀ r, InnerProductSpace ℝ (G r)]
  [∀ r, NormedAddCommGroup (E r)] [∀ r, InnerProductSpace ℝ (E r)]

theorem l2_norm_sq (x : lp G 2) : ‖x‖^2=∑' r, ‖x r‖^2 := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x

theorem l2_summable_sq (x : lp G 2) : Summable (fun r => ‖x r‖^2) := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

def tailLinear : lp G 2 →ₗ[ℝ] lp (fun r => G (r+1)) 2 where
  toFun x := ⟨fun r => x (r+1), memℓp_gen (by
    exact ((lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).comp_injective
      Nat.succ_injective)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tailLinear_norm_le (x : lp G 2) : ‖tailLinear x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [l2_norm_sq,l2_norm_sq]
  change (∑' r, ‖x (r+1)‖^2) ≤ ∑' r, ‖x r‖^2
  exact tsum_comp_le_tsum_of_inj (l2_summable_sq x) (fun _ => sq_nonneg _) Nat.succ_injective

def tail : lp G 2 →L[ℝ] lp (fun r => G (r+1)) 2 :=
  tailLinear.mkContinuous 1 (by intro x; simpa using tailLinear_norm_le x)

@[simp] theorem tail_apply (x : lp G 2) (r : ℕ) : tail x r=x (r+1) := rfl

def diagonal (L : ∀ r, E r →L[ℝ] G r) {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ r, ‖L r‖ ≤ C) : lp E 2 →L[ℝ] lp G 2 := lp.mapCLM 2 L hC hL

@[simp] theorem diagonal_apply (L : ∀ r, E r →L[ℝ] G r) {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ r, ‖L r‖ ≤ C) (x : lp E 2) (r : ℕ) :
    diagonal L hC hL x r=L r (x r) := rfl

theorem norm_diagonal_le (L : ∀ r, E r →L[ℝ] G r) {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ r, ‖L r‖ ≤ C) : ‖diagonal L hC hL‖ ≤ C :=
  lp.norm_mapCLM_le 2 L hC hL

def shift (J : ∀ r, G (r+1) →L[ℝ] G r) {C : ℝ} (hC : 0 ≤ C)
    (hJ : ∀ r, ‖J r‖ ≤ C) : lp G 2 →L[ℝ] lp G 2 :=
  (diagonal J hC hJ).comp tail

@[simp] theorem shift_apply (J : ∀ r, G (r+1) →L[ℝ] G r) {C : ℝ} (hC : 0 ≤ C)
    (hJ : ∀ r, ‖J r‖ ≤ C) (x : lp G 2) (r : ℕ) :
    shift J hC hJ x r=J r (x (r+1)) := rfl

theorem norm_shift_le (J : ∀ r, G (r+1) →L[ℝ] G r) {C : ℝ} (hC : 0 ≤ C)
    (hJ : ∀ r, ‖J r‖ ≤ C) : ‖shift J hC hJ‖ ≤ C := by
  apply (shift J hC hJ).opNorm_le_bound hC
  intro x
  exact ((diagonal J hC hJ).le_of_opNorm_le (norm_diagonal_le _ hC hJ) _).trans
    (mul_le_mul_of_nonneg_left (tailLinear_norm_le x) hC)

theorem diagonal_single (L : ∀ r, E r →L[ℝ] G r) {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ r, ‖L r‖ ≤ C) (r : ℕ) (y : E r) :
    diagonal L hC hL (lp.single 2 r y)=lp.single 2 r (L r y) := by
  ext j
  by_cases h : j=r
  · subst j; simp
  · simp [h]

theorem shift_single_succ (J : ∀ r, G (r+1) →L[ℝ] G r) {C : ℝ} (hC : 0 ≤ C)
    (hJ : ∀ r, ‖J r‖ ≤ C) (r : ℕ) (y : G (r+1)) :
    shift J hC hJ (lp.single 2 (r+1) y)=lp.single 2 r (J r y) := by
  ext j
  by_cases h : j=r
  · subst j; simp
  · simp [h]

theorem norm_block_le_diagonal (L : ∀ r, E r →L[ℝ] G r) {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ r, ‖L r‖ ≤ C) (r : ℕ) : ‖L r‖ ≤ ‖diagonal L hC hL‖ := by
  apply (L r).opNorm_le_bound (norm_nonneg _)
  intro y
  have he := (diagonal L hC hL).le_opNorm (lp.single 2 r y)
  simpa only [diagonal_single,lp.norm_single (by norm_num : 0 < (2 : ℝ≥0∞))] using he

theorem norm_block_le_shift (J : ∀ r, G (r+1) →L[ℝ] G r) {C : ℝ} (hC : 0 ≤ C)
    (hJ : ∀ r, ‖J r‖ ≤ C) (r : ℕ) : ‖J r‖ ≤ ‖shift J hC hJ‖ := by
  apply (J r).opNorm_le_bound (norm_nonneg _)
  intro y
  have he := (shift J hC hJ).le_opNorm (lp.single 2 (r+1) y)
  simpa only [shift_single_succ,lp.norm_single (by norm_num : 0 < (2 : ℝ≥0∞))] using he

variable [∀ r, CompleteSpace (G r)] [∀ r, CompleteSpace (E r)]

theorem diagonal_adjoint_apply (L : ∀ r, E r →L[ℝ] G r) {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ r, ‖L r‖ ≤ C) (x : lp G 2) (r : ℕ) :
    (diagonal L hC hL).adjoint x r=(L r).adjoint (x r) := by
  apply ext_inner_right ℝ
  intro y
  have he := adjoint_inner_left (diagonal L hC hL) (lp.single 2 r y) x
  rw [lp.inner_single_right] at he
  have hs : diagonal L hC hL (lp.single 2 r y)=lp.single 2 r (L r y) := by
    ext j
    by_cases h : j=r
    · subst j; simp
    · simp [h]
  rw [hs,lp.inner_single_right] at he
  exact he.trans (adjoint_inner_left (L r) y (x r)).symm

theorem shift_adjoint_zero (J : ∀ r, G (r+1) →L[ℝ] G r) {C : ℝ} (hC : 0 ≤ C)
    (hJ : ∀ r, ‖J r‖ ≤ C) (x : lp G 2) : (shift J hC hJ).adjoint x 0=0 := by
  apply ext_inner_right ℝ
  intro y
  have he := adjoint_inner_left (shift J hC hJ) (lp.single 2 0 y) x
  rw [lp.inner_single_right] at he
  have hs : shift J hC hJ (lp.single 2 0 y)=0 := by ext j; simp
  simpa [hs] using he

theorem shift_adjoint_succ (J : ∀ r, G (r+1) →L[ℝ] G r) {C : ℝ} (hC : 0 ≤ C)
    (hJ : ∀ r, ‖J r‖ ≤ C) (x : lp G 2) (r : ℕ) :
    (shift J hC hJ).adjoint x (r+1)=(J r).adjoint (x r) := by
  apply ext_inner_right ℝ
  intro y
  have he := adjoint_inner_left (shift J hC hJ) (lp.single 2 (r+1) y) x
  rw [lp.inner_single_right] at he
  have hs : shift J hC hJ (lp.single 2 (r+1) y)=lp.single 2 r (J r y) := by
    ext j
    by_cases h : j=r
    · subst j; simp
    · simp [h]
  rw [hs,lp.inner_single_right] at he
  exact he.trans (adjoint_inner_left (J r) y (x r)).symm

#print axioms norm_shift_le
#print axioms diagonal_adjoint_apply
#print axioms shift_adjoint_zero
#print axioms shift_adjoint_succ
end GradedHilbert
end KLSBelow25

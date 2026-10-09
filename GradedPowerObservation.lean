import GradedHilbertOperators

/-! Exact block localization of powers of the genuine graded shift. In
particular, uniform bounds on repeated-integration blocks are equivalent
to the corresponding bound on the full observation operator. -/
noncomputable section
namespace KLSBelow25.GradedHilbert
open ContinuousLinearMap
open scoped ENNReal
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {G E : ℕ → Type*}
  [∀ r, NormedAddCommGroup (G r)] [∀ r, InnerProductSpace ℝ (G r)]
  [∀ r, NormedAddCommGroup (E r)] [∀ r, InnerProductSpace ℝ (E r)]
  (J : ∀ r, G (r+1) →L[ℝ] G r) (L : ∀ r, E r →L[ℝ] G r)
  {CJ CL : ℝ} (hCJ : 0 ≤ CJ) (hJ : ∀ r, ‖J r‖ ≤ CJ)
  (hCL : 0 ≤ CL) (hL : ∀ r, ‖L r‖ ≤ CL)

theorem shift_power_depends (d r : ℕ) (x y : lp G 2)
    (hxy : x (r+d)=y (r+d)) :
    ((shift J hCJ hJ)^d) x r=((shift J hCJ hJ)^d) y r := by
  induction d generalizing r with
  | zero => simpa using hxy
  | succ d ih =>
    rw [pow_succ',mul_apply_eq_comp,mul_apply_eq_comp,
      shift_apply,shift_apply]
    congr 1
    apply ih (r+1)
    rw [show r+1+d=r+(d+1) by omega]
    exact hxy

def powerObservationBlock (d r : ℕ) : E (r+d) →L[ℝ] G r :=
  (lp.evalCLM ℝ G 2 r).comp
    ((((shift J hCJ hJ)^d).comp (diagonal L hCL hL)).comp
      (lp.singleContinuousLinearMap ℝ E 2 (r+d)))

@[simp] theorem powerObservationBlock_apply (d r : ℕ) (v : E (r+d)) :
    powerObservationBlock J L hCJ hJ hCL hL d r v =
      (((shift J hCJ hJ)^d).comp (diagonal L hCL hL)) (lp.single 2 (r+d) v) r := rfl

theorem power_observation_apply (d r : ℕ) (x : lp E 2) :
    (((shift J hCJ hJ)^d).comp (diagonal L hCL hL)) x r =
      powerObservationBlock J L hCJ hJ hCL hL d r (x (r+d)) := by
  apply shift_power_depends
  simp

theorem norm_powerObservationBlock_le (d r : ℕ) :
    ‖powerObservationBlock J L hCJ hJ hCL hL d r‖ ≤
      ‖((shift J hCJ hJ)^d).comp (diagonal L hCL hL)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  calc
    _ ≤ ‖(((shift J hCJ hJ)^d).comp (diagonal L hCL hL))
        (lp.single 2 (r+d) v)‖ := lp.norm_apply_le_norm (by norm_num) _ r
    _ ≤ ‖((shift J hCJ hJ)^d).comp (diagonal L hCL hL)‖ *
        ‖lp.single 2 (r+d) v‖ := ContinuousLinearMap.le_opNorm _ _
    _ = _ := by rw [lp.norm_single (by norm_num : 0 < (2 : ℝ≥0∞))]

theorem norm_power_observation_le_of_blocks (d : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ r, ‖powerObservationBlock J L hCJ hJ hCL hL d r‖ ≤ C) :
    ‖((shift J hCJ hJ)^d).comp (diagonal L hCL hL)‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  rw [l2_norm_sq,mul_pow,l2_norm_sq]
  calc
    _ ≤ ∑' r, C^2 * ‖x (r+d)‖^2 := by
      apply Summable.tsum_le_tsum
      · intro r
        rw [power_observation_apply]
        simpa only [mul_pow] using
          (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg (x (r+d))))).mpr
            ((powerObservationBlock J L hCJ hJ hCL hL d r).le_of_opNorm_le (hb r) (x (r+d)))
      · exact l2_summable_sq _
      · exact ((l2_summable_sq x).comp_injective (fun a b h => Nat.add_right_cancel h)).mul_left _
    _ = C^2 * ∑' r, ‖x (r+d)‖^2 := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (tsum_comp_le_tsum_of_inj (l2_summable_sq x) (fun _ => sq_nonneg _)
        (fun a b h => Nat.add_right_cancel h)) (sq_nonneg C)

theorem norm_power_observation_le_iff (d : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    ‖((shift J hCJ hJ)^d).comp (diagonal L hCL hL)‖ ≤ C ↔
      ∀ r, ‖powerObservationBlock J L hCJ hJ hCL hL d r‖ ≤ C := by
  exact ⟨fun h r => (norm_powerObservationBlock_le J L hCJ hJ hCL hL d r).trans h,
    norm_power_observation_le_of_blocks J L hCJ hJ hCL hL d hC⟩

end KLSBelow25.GradedHilbert
#print axioms KLSBelow25.GradedHilbert.power_observation_apply
#print axioms KLSBelow25.GradedHilbert.norm_power_observation_le_iff

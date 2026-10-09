import LocalHeatMaximumPrinciple

/-! A genuine joint second-variation estimate. Its hypotheses identify the
test-test and law-test blocks of the actual Hessian; they are not an Appell
mixed-surplus estimate. -/
noncomputable section
open InnerProductSpace
open scoped ContDiff Topology
namespace KLSBelow25
open KLS.DeterministicBridgeNext
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 theorem joint_maximum_schur_correction
    {F : E × H → ℝ}
    (hF : ContDiffAt ℝ (⊤ : ℕ∞) F 0) (hmax : IsLocalMax F 0)
    (v : E) (b : H) {lam : ℝ} (hlam : 0 < lam)
    (hmixed : ∀ ell : H,
      (fderiv ℝ (fderiv ℝ F) 0 (v,0)) (0,ell)+
        (fderiv ℝ (fderiv ℝ F) 0 (0,ell)) (v,0) = 4*⟪b,ell⟫_ℝ)
    (htest : ∀ ell : H,
      -(2*lam)*‖ell‖^2 ≤ (fderiv ℝ (fderiv ℝ F) 0 (0,ell)) (0,ell)) :
    (fderiv ℝ (fderiv ℝ F) 0 (v,0)) (v,0)/2+‖b‖^2/lam ≤ 0 := by
  let Q := fderiv ℝ (fderiv ℝ F) (0 : E × H)
  have hD : DifferentiableAt ℝ (fderiv ℝ F) (0 : E × H) :=
    (hF.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp)
  have hnonpos (w : E × H) : Q w w ≤ 0 := by
    have hh := fderiv_fderiv_nonpos_of_localMax hmax hF w
    rw [fderiv_clm_apply hD (differentiableAt_const w)] at hh
    simpa [Q] using hh
  let ell : H := (1/lam) • b
  have hw : (v,ell) = (v,0)+(0,ell) := by simp
  have hn := hnonpos (v,ell)
  simp only [hw,map_add,ContinuousLinearMap.add_apply] at hn
  have hm := hmixed ell
  have ht := htest ell
  change Q (v,0) (0,ell)+Q (0,ell) (v,0) = _ at hm
  change _ ≤ Q (0,ell) (0,ell) at ht
  have hcore : Q (v,0) (v,0)+4*⟪b,ell⟫_ℝ-(2*lam)*‖ell‖^2 ≤ 0 := by
    linarith
  have hpositive : 0 < 1/lam := one_div_pos.mpr hlam
  simp only [ell,inner_smul_right,real_inner_self_eq_norm_sq,norm_smul,
    Real.norm_eq_abs,abs_of_pos hpositive] at hcore
  change Q (v,0) (v,0)/2+‖b‖^2/lam ≤ 0
  have hid : 4*((1/lam)*‖b‖^2)-(2*lam)*((1/lam)*‖b‖)^2 = 2*(‖b‖^2/lam) := by
    field_simp [hlam.ne']
    <;> ring
  rw [show Q (v,0) (v,0)+4*((1/lam)*‖b‖^2)-(2*lam)*((1/lam)*‖b‖)^2 =
      Q (v,0) (v,0)+(4*((1/lam)*‖b‖^2)-(2*lam)*((1/lam)*‖b‖)^2) by ring,hid] at hcore
  linarith

 theorem joint_maximum_probe_correction
    {F : E × H → ℝ}
    (hF : ContDiffAt ℝ (⊤ : ℕ∞) F 0) (hmax : IsLocalMax F 0)
    (v : E) (ell : H) {beta D : ℝ} (hDpos : 0 < D)
    (hmixed : (fderiv ℝ (fderiv ℝ F) 0 (v,0)) (0,ell)+
        (fderiv ℝ (fderiv ℝ F) 0 (0,ell)) (v,0) = 4*beta)
    (htest : (fderiv ℝ (fderiv ℝ F) 0 (0,ell)) (0,ell) = -2*D) :
    (fderiv ℝ (fderiv ℝ F) 0 (v,0)) (v,0)/2+beta^2/D ≤ 0 := by
  let Q := fderiv ℝ (fderiv ℝ F) (0 : E × H)
  have hDf : DifferentiableAt ℝ (fderiv ℝ F) (0 : E × H) :=
    (hF.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp)
  have hnonpos (z : E × H) : Q z z ≤ 0 := by
    have hh := fderiv_fderiv_nonpos_of_localMax hmax hF z
    rw [fderiv_clm_apply hDf (differentiableAt_const z)] at hh
    simpa [Q] using hh
  let c : ℝ := beta/D
  have hw : (v,c • ell) = (v,0)+c • (0,ell) := by simp
  have hn := hnonpos (v,c • ell)
  simp only [hw,map_add,map_smul,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul] at hn
  change Q (v,0) (0,ell)+Q (0,ell) (v,0) = 4*beta at hmixed
  change Q (0,ell) (0,ell) = -2*D at htest
  rw [htest] at hn
  have hmc := congrArg (fun x : ℝ => c*x) hmixed
  have hcore : Q (v,0) (v,0)+4*c*beta-2*c^2*D ≤ 0 := by
    nlinarith [hmc]
  have hid : 4*c*beta-2*c^2*D = 2*(beta^2/D) := by
    dsimp only [c]
    field_simp [hDpos.ne']
    <;> ring
  have hh : Q (v,0) (v,0)+2*(beta^2/D) ≤ 0 := by
    linarith [hid]
  change Q (v,0) (v,0)/2+beta^2/D ≤ 0
  linarith

end KLSBelow25
#print axioms KLSBelow25.joint_maximum_schur_correction
#print axioms KLSBelow25.joint_maximum_probe_correction

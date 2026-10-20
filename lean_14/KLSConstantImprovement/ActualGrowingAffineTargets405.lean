import KLS.DampedWhiteningWeakLimit
import KLS.RegularMomentMapQuadratic
import KLS.PositiveMatrixPerturbation
import KLS.AffinePotentialCutoff

/-! Every fixed target ball is eventually strictly interior to an expanding
ball after actual affine maps tending to the identity.  This supplies compact
source pullback supports without any full-support source assumption. -/
noncomputable section
open Set Filter Matrix Metric
open scoped Topology NNReal
namespace KLSConstantImprovement.ActualGrowingAffineTargets405
open KLS
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem affine_ball_contains_closedBall_of_near_one
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) (hA : A.det ≠ 0)
    (hnear : ‖matrixAction A - ContinuousLinearMap.id ℝ (Space n)‖ ≤ (1/2 : ℝ))
    (hb : ‖b‖ ≤ 1) {R r : ℝ} (hr : 2*(R+1) < r) :
    closedBall (0 : Space n) R ⊆ (affineMatrixEquiv A b hA) '' ball 0 r := by
  intro y hy
  let e := affineMatrixEquiv A b hA
  let x := e.symm y
  have hxy : matrixAction A x + b = y := e.apply_symm_apply y
  have hlin : ‖matrixAction A x - x‖ ≤ (1/2 : ℝ)*‖x‖ := by
    have hh := (matrixAction A - ContinuousLinearMap.id ℝ (Space n)).le_opNorm x
    change ‖matrixAction A x - x‖ ≤ ‖matrixAction A - ContinuousLinearMap.id ℝ (Space n)‖ * ‖x‖ at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hnear (norm_nonneg x))
  have hnorm : ‖x‖ ≤ 2 * ‖matrixAction A x‖ := by
    have hh := norm_le_norm_sub_add x (matrixAction A x)
    rw [norm_sub_rev] at hh
    linarith
  have hAx : ‖matrixAction A x‖ ≤ R+1 := by
    have he : matrixAction A x = y-b := (eq_sub_iff_add_eq).mpr hxy
    rw [he]
    have hy' : ‖y‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hy
    exact (norm_sub_le y b).trans (add_le_add hy' hb)
  refine ⟨x, ?_, e.apply_symm_apply y⟩
  rw [mem_ball, dist_zero_right]
  exact lt_of_le_of_lt (hnorm.trans (mul_le_mul_of_nonneg_left hAx (by norm_num))) hr

theorem eventually_fixed_ball_interior_growing_affine
    {A : ℕ → Matrix (Fin n) (Fin n) ℝ} {b : ℕ → Space n}
    (hcoeff : ∀ i j, Tendsto (fun k => affineCoordinateCoefficient (A k) (b k) i j)
      atTop (𝓝 (affineCoordinateCoefficient 1 0 i j))) (R : ℝ) :
    ∀ᶠ k in atTop, ∀ hA : (A k).det ≠ 0,
      closedBall (0 : Space n) R ⊆
        interior (closure ((affineMatrixEquiv (A k) (b k) hA) '' ball 0 ((k : ℝ)+1))) := by
  have hmat : Tendsto A atTop (𝓝 (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    simpa only [affineCoordinateCoefficient] using hcoeff i (some j)
  have hid : matrixAction (1 : Matrix (Fin n) (Fin n) ℝ) = ContinuousLinearMap.id ℝ (Space n) := by
    apply ContinuousLinearMap.ext
    intro x
    exact matrixAction_one_apply x
  have hn : Tendsto (fun k => ‖matrixAction (A k) - ContinuousLinearMap.id ℝ (Space n)‖)
      atTop (𝓝 0) := by
    have hh := ((continuous_matrixAction.continuousAt.tendsto.comp hmat).sub
      (tendsto_const_nhds (x := matrixAction (1 : Matrix (Fin n) (Fin n) ℝ)))).norm
    simpa only [hid, sub_self, norm_zero, Function.comp_def] using hh
  have hb : Tendsto (fun k => ‖b k‖) atTop (𝓝 0) := by
    have hh := (tendsto_affineMatrixMap_of_coefficients hcoeff (0 : Space n)).norm
    simpa only [affineMatrixMap_apply, map_zero, zero_add, norm_zero] using hh
  have hnat : Tendsto (fun k : ℕ => (k : ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun k : ℕ => le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
      tendsto_natCast_atTop_atTop
  filter_upwards [hn.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/2)),
    hb.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    hnat.eventually_gt_atTop (2*(R+1))] with k hk hbk hrk hAk
  let e := affineMatrixEquiv (A k) (b k) hAk
  have hsub := affine_ball_contains_closedBall_of_near_one (A k) (b k) hAk hk.le hbk.le hrk
  exact hsub.trans ((e.toHomeomorph.isOpenMap _ isOpen_ball).subset_interior_closure)

end KLSConstantImprovement.ActualGrowingAffineTargets405
#print axioms KLSConstantImprovement.ActualGrowingAffineTargets405.affine_ball_contains_closedBall_of_near_one
#print axioms KLSConstantImprovement.ActualGrowingAffineTargets405.eventually_fixed_ball_interior_growing_affine

import ActualProjectionOrbitSlack
import ProjectionSharedResourceSlack

/-! The exact linear-projection fraction of the orthogonal orbit residual.
This improves one genuine intermediate coefficient in the existing recurrence.
It does not assert a new numerical Poincare endpoint. -/
noncomputable section
open MeasureTheory Matrix InnerProductSpace ContinuousLinearMap
open scoped ContDiff ENNReal
namespace KLSConstantImprovement.ProjectionResidualCovariance
open KLS KLS.DeterministicBridgeIntegration KLSBelow25.ProjectionOrbitSlack
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

section Hilbert
variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

theorem projection_residual_norm_exact (P : H →L[ℝ] H)
    (hinner : ∀ x : H, inner ℝ x (P x) = ‖P x‖ ^ 2)
    (v : H) (hv : 0 < ‖v‖ ^ 2) :
    ‖P v - (‖P v‖ ^ 2 / ‖v‖ ^ 2) • v‖ ^ 2 =
      (1 - ‖P v‖ ^ 2 / ‖v‖ ^ 2) * ‖P v‖ ^ 2 := by
  rw [projection_residual_norm_sq P hinner]
  field_simp [hv.ne']
  ring

theorem projection_of_residual_norm_exact (P : H →L[ℝ] H)
    (hinner : ∀ x : H, inner ℝ x (P x) = ‖P x‖ ^ 2)
    (hidem : ∀ x : H, P (P x) = P x)
    (v : H) (hv : 0 < ‖v‖ ^ 2) :
    ‖P (P v - (‖P v‖ ^ 2 / ‖v‖ ^ 2) • v)‖ ^ 2 =
      (1 - ‖P v‖ ^ 2 / ‖v‖ ^ 2) *
        ‖P v - (‖P v‖ ^ 2 / ‖v‖ ^ 2) • v‖ ^ 2 := by
  have he : P (P v - (‖P v‖ ^ 2 / ‖v‖ ^ 2) • v) =
      (1 - ‖P v‖ ^ 2 / ‖v‖ ^ 2) • P v := by
    rw [map_sub, map_smul, hidem, sub_smul, one_smul]
  rw [he, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    projection_residual_norm_exact P hinner v hv]
  ring

/-- The projection contribution is exactly `1-c`, not the generic upper
bound one, where c is the projection fraction of the original orbit vector. -/
theorem projection_residual_shared_energy_le (R P : H →L[ℝ] H)
    (hinner : ∀ x : H, inner ℝ x (P x) = ‖P x‖ ^ 2)
    (hidem : ∀ x : H, P (P x) = P x)
    (v : H) (hv : 0 < ‖v‖ ^ 2) :
    let c := ‖P v‖ ^ 2 / ‖v‖ ^ 2
    let y := P v - c • v
    ‖R.adjoint y‖ ^ 2 + ‖P y‖ ^ 2 ≤
      (‖R‖ ^ 2 + 1 - c) * ‖y‖ ^ 2 := by
  dsimp only
  have hr := pow_le_pow_left₀ (norm_nonneg _)
    (R.adjoint.le_opNorm (P v - (‖P v‖ ^ 2 / ‖v‖ ^ 2) • v)) 2
  rw [adjoint.norm_map, mul_pow] at hr
  rw [projection_of_residual_norm_exact P hinner hidem v hv]
  nlinarith only [hr]

/-- The exact projection fraction can be retained through the shared-resource
Cauchy estimate, improving `norm R squared + 1` to `norm R squared + 1 - c`.
This is a universal Hilbert inequality under the displayed actual-projection
and curvature comparison hypotheses. -/
theorem projection_variance_le_refined_shared_resource (R P : H →L[ℝ] H)
    (hP : P.adjoint = P)
    (hinner : ∀ x : H, inner ℝ x (P x) = ‖P x‖ ^ 2)
    (hidem : ∀ x : H, P (P x) = P x)
    (hPnorm : ∀ x : H, ‖P x‖ ≤ ‖x‖)
    (hcomp : ∀ x : H, ‖R x‖ ^ 2 ≤ ‖R.adjoint x‖ ^ 2 + ‖P x‖ ^ 2)
    (u v w : H) (rho sigma : ℝ) (hv : v = R.adjoint u) (hw : w = R.adjoint v)
    (hvpos : 0 < ‖v‖ ^ 2) {omega zeta : ℝ} (ho : 0 < omega) (hz : 0 < zeta) :
    let c := ‖P v‖ ^ 2 / ‖v‖ ^ 2
    ‖P v‖ ^ 2 - (‖P v‖ ^ 2) ^ 2 / ‖v‖ ^ 2 ≤
      ((‖R‖ ^ 2 + 1 - c) / omega + 1 / zeta) *
        (omega * (‖R v - rho • u‖ ^ 2 + inner ℝ v (defect R P v)) +
          zeta * ‖R w - sigma • v‖ ^ 2) := by
  let D := defect R P
  let x := R v - rho • u
  let next := R w - sigma • v
  let c := ‖P v‖ ^ 2 / ‖v‖ ^ 2
  let y := P v - c • v
  let V := ‖P v‖ ^ 2 - (‖P v‖ ^ 2) ^ 2 / ‖v‖ ^ 2
  have hD : D.adjoint = D := by
    dsimp [D, defect]
    simp only [map_sub, map_add, adjoint_comp, adjoint_adjoint, hP]
  have hDpos (z : H) : 0 ≤ inner ℝ z (D z) := by
    dsimp [D]
    rw [defect_quadratic R P hinner]
    linarith [hcomp z]
  have hc1 : c ≤ 1 := (div_le_one hvpos).mpr
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hPnorm v))
  have hcoef : 0 ≤ ‖R‖ ^ 2 + 1 - c := by nlinarith [sq_nonneg ‖R‖]
  have hyv : inner ℝ y v = 0 := by
    dsimp [y, c]
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      ← real_inner_comm (P v) v, hinner, div_mul_cancel₀ _ hvpos.ne']
    ring
  have hynorm : ‖y‖ ^ 2 = V := by
    rw [show y = P v - c • v by rfl, projection_residual_norm_sq P hinner]
    dsimp [c, V]
    field_simp
    ring
  have hyP : inner ℝ y (P v) = V := by
    dsimp [y, V, c]
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hinner]
    ring
  have hpair : V = inner ℝ (R y) x + inner ℝ y (D v) - inner ℝ y next := by
    have hh := congrArg (fun z : H => inner ℝ y z)
      (projection_orbit_residual_identity R P u v w rho sigma hv hw)
    rw [hyP] at hh
    simp only [inner_add_right, inner_sub_right, real_inner_smul_right,
      hyv, mul_zero, zero_add] at hh
    rw [adjoint_inner_right] at hh
    dsimp [D, x, next] at hh ⊢
    simp only [inner_sub_right, real_inner_smul_right, hyv, mul_zero] at hh ⊢
    linarith
  have hV : 0 ≤ V := hynorm ▸ sq_nonneg ‖y‖
  have ht : 0 ≤ ‖x‖ ^ 2 + inner ℝ v (D v) :=
    add_nonneg (sq_nonneg _) (hDpos v)
  have hC : ‖R y‖ ^ 2 + inner ℝ y (D y) ≤ (‖R‖ ^ 2 + 1 - c) * V := by
    have he := defect_quadratic R P hinner y
    have hs := projection_residual_shared_energy_le R P hinner hidem v hvpos
    change ‖R.adjoint y‖ ^ 2 + ‖P y‖ ^ 2 ≤
      (‖R‖ ^ 2 + 1 - c) * ‖y‖ ^ 2 at hs
    change inner ℝ y (D y) = _ at he
    rw [hynorm] at hs
    linarith
  have hfirst := (psd_block_cauchy_square D hD hDpos (R y) x y v).trans
    (mul_le_mul_of_nonneg_right hC ht)
  have hlast := pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm y next) 2
  rw [sq_abs, mul_pow, hynorm] at hlast
  have hfirst' : (inner ℝ (R y) x + inner ℝ y (D v)) ^ 2 ≤
      ((‖R‖ ^ 2 + 1 - c) * V / omega) *
        (omega * (‖x‖ ^ 2 + inner ℝ v (D v))) := by
    convert hfirst using 1
    field_simp
  have hlast' : (-inner ℝ y next) ^ 2 ≤ (V / zeta) * (zeta * ‖next‖ ^ 2) := by
    rw [neg_sq]
    convert hlast using 1
    field_simp
  have hh := two_real_sq_le (a := inner ℝ (R y) x + inner ℝ y (D v))
    (b := -inner ℝ y next)
    (div_nonneg (mul_nonneg hcoef hV) ho.le) (div_nonneg hV hz.le)
    (mul_nonneg ho.le ht) (by positivity : 0 ≤ zeta * ‖next‖ ^ 2) hfirst' hlast'
  rw [← sub_eq_add_neg, ← hpair] at hh
  have he : ((‖R‖ ^ 2 + 1 - c) * V / omega + V / zeta) *
      (omega * (‖x‖ ^ 2 + inner ℝ v (D v)) + zeta * ‖next‖ ^ 2) =
      V * (((‖R‖ ^ 2 + 1 - c) / omega + 1 / zeta) *
        (omega * (‖x‖ ^ 2 + inner ℝ v (D v)) + zeta * ‖next‖ ^ 2)) := by ring
  rw [he] at hh
  by_cases h0 : V = 0
  · change V ≤ _
    rw [h0]
    exact mul_nonneg (add_nonneg (div_nonneg hcoef ho.le) (by positivity))
      (add_nonneg (mul_nonneg ho.le ht) (by positivity))
  · have hv' : 0 < V := lt_of_le_of_ne hV (Ne.symm h0)
    have hc : V * V ≤ V * (((‖R‖ ^ 2 + 1 - c) / omega + 1 / zeta) *
        (omega * (‖x‖ ^ 2 + inner ℝ v (D v)) + zeta * ‖next‖ ^ 2)) := by
      simpa only [pow_two] using hh
    exact le_of_mul_le_mul_left hc hv'

end Hilbert

variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ),
    κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
  (hiso : IsIsotropic (potentialMeasure φ))

theorem actual_projection_residual_shared_energy_le
    (v : GradedCenteredTensorHilbert hφ) (hv : 0 < ‖v‖ ^ 2) :
    let R := gradedTensorIntegration hφ hκ hlower
    let P := gradedLinearTensorProjection hφ hκ hlower hiso
    let c := ‖P v‖ ^ 2 / ‖v‖ ^ 2
    let y := P v - c • v
    ‖R.adjoint y‖ ^ 2 + ‖P y‖ ^ 2 ≤
      (‖R‖ ^ 2 + 1 - c) * ‖y‖ ^ 2 :=
  projection_residual_shared_energy_le
    (gradedTensorIntegration hφ hκ hlower)
    (gradedLinearTensorProjection hφ hκ hlower hiso)
    (gradedLinearTensorProjection_inner hφ hκ hlower hiso)
    (gradedLinearTensorProjection_idempotent hφ hκ hlower hiso) v hv

theorem actual_projection_variance_le_refined_shared_resource
    (u v w : GradedCenteredTensorHilbert hφ) (rho sigma : ℝ)
    (hv : v = (gradedTensorIntegration hφ hκ hlower).adjoint u)
    (hw : w = (gradedTensorIntegration hφ hκ hlower).adjoint v)
    (hvpos : 0 < ‖v‖ ^ 2) {omega zeta : ℝ} (ho : 0 < omega) (hz : 0 < zeta) :
    let R := gradedTensorIntegration hφ hκ hlower
    let P := gradedLinearTensorProjection hφ hκ hlower hiso
    let c := ‖P v‖ ^ 2 / ‖v‖ ^ 2
    ‖P v‖ ^ 2 - (‖P v‖ ^ 2) ^ 2 / ‖v‖ ^ 2 ≤
      ((‖R‖ ^ 2 + 1 - c) / omega + 1 / zeta) *
        (omega * (‖R v - rho • u‖ ^ 2 + inner ℝ v (defect R P v)) +
          zeta * ‖R w - sigma • v‖ ^ 2) :=
  projection_variance_le_refined_shared_resource
    (gradedTensorIntegration hφ hκ hlower)
    (gradedLinearTensorProjection hφ hκ hlower hiso)
    (gradedLinearTensorProjection_adjoint hφ hκ hlower hiso)
    (gradedLinearTensorProjection_inner hφ hκ hlower hiso)
    (gradedLinearTensorProjection_idempotent hφ hκ hlower hiso)
    (gradedLinearTensorProjection_norm_le hφ hκ hlower hiso)
    (actual_graded_linear_projection_comparison hφ hκ hlower hiso)
    u v w rho sigma hv hw hvpos ho hz

end KLSConstantImprovement.ProjectionResidualCovariance
#print axioms KLSConstantImprovement.ProjectionResidualCovariance.projection_residual_norm_exact
#print axioms KLSConstantImprovement.ProjectionResidualCovariance.projection_of_residual_norm_exact
#print axioms KLSConstantImprovement.ProjectionResidualCovariance.projection_residual_shared_energy_le
#print axioms KLSConstantImprovement.ProjectionResidualCovariance.projection_variance_le_refined_shared_resource
#print axioms KLSConstantImprovement.ProjectionResidualCovariance.actual_projection_residual_shared_energy_le
#print axioms KLSConstantImprovement.ProjectionResidualCovariance.actual_projection_variance_le_refined_shared_resource

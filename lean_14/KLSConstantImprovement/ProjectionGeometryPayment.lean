import KLSConstantImprovement.ProjectionResidualCovariance
import ActualIndividualObservationCaps

/-! Retain the exact projection fraction through normalization and the scalar
payment.  The earlier shared-resource and endpoint files are unchanged. -/
noncomputable section
open MeasureTheory Matrix InnerProductSpace ContinuousLinearMap
open scoped ContDiff ENNReal
namespace KLSConstantImprovement.ProjectionGeometryPayment
open KLS KLS.DeterministicBridgeIntegration KLSBelow25.ProjectionOrbitSlack
open KLSConstantImprovement.ProjectionResidualCovariance
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- This normalization also covers a terminating orbit: its second numerator
must vanish when the second denominator vanishes. -/
theorem weighted_slack_normalize_zero {S u v t₁ t₂ V M omega : ℝ}
    (hS : 0 < S) (hu : 0 < u) (hv : 0 ≤ v) (homega : 0 < omega) (homega1 : omega < 1)
    (ht₂ : 0 ≤ t₂) (hM : 0 ≤ M) (hvu : v ≤ S * u)
    (hzero : v = 0 → t₂ = 0)
    (hraw : V ≤ M * (omega * t₁ + ((1 - omega) / S) * t₂)) :
    V / u ≤ M * (omega * (t₁ / u) + (1 - omega) * (t₂ / v)) := by
  by_cases hv0 : v = 0
  · have ht0 := hzero hv0
    have hh := div_le_div_of_nonneg_right hraw hu.le
    rw [ht0] at hh ⊢
    simp only [mul_zero, add_zero, zero_div] at hh ⊢
    convert hh using 1 <;> ring
  · exact weighted_slack_normalize hS hu (lt_of_le_of_ne hv (Ne.symm hv0))
      homega homega1 ht₂ hM hvu hraw

/-- The scalar denominator comparison.  In particular no nonnegativity
assumption on eta is needed, and q=1 is included. -/
theorem payment_of_refined_variance {S omega b q η W : ℝ}
    (hS : 0 < S) (homega : 0 < omega) (homega1 : omega < 1)
    (hb : 0 ≤ b) (hbq : b ≤ q) (hq : q ≤ 1)
    (hvar : b * (1 - b) ≤ ((S + 1 - b) / omega + S / (1 - omega)) * W)
    (hcoefficient : η * ((S + 1 - q) / omega + S / (1 - omega)) ≤ 1 - q) :
    η * b ≤ W := by
  let Mb := (S + 1 - b) / omega + S / (1 - omega)
  let Mq := (S + 1 - q) / omega + S / (1 - omega)
  have h1omega : 0 < 1 - omega := sub_pos.mpr homega1
  have hMb : 0 < Mb := by
    dsimp [Mb]
    have htop : 0 < S + 1 - b := by linarith
    positivity
  have hMq : 0 < Mq := by
    dsimp [Mq]
    have htop : 0 < S + 1 - q := by linarith
    positivity
  have hid : (1 - b) * Mq - (1 - q) * Mb =
      (q - b) * S / (omega * (1 - omega)) := by
    dsimp [Mb, Mq]
    field_simp
    ring
  have hratio : (1 - q) * Mb ≤ (1 - b) * Mq := by
    have hh : 0 ≤ (q - b) * S / (omega * (1 - omega)) :=
      div_nonneg (mul_nonneg (sub_nonneg.mpr hbq) hS.le)
        (mul_nonneg homega.le h1omega.le)
    linarith only [hid, hh]
  have hη : η * Mb ≤ 1 - b := by
    have hh := (mul_le_mul_of_nonneg_right hcoefficient hMb.le).trans hratio
    change (η * Mq) * Mb ≤ (1 - b) * Mq at hh
    have hh' : (η * Mb) * Mq ≤ (1 - b) * Mq := by nlinarith only [hh]
    exact le_of_mul_le_mul_right hh' hMq
  have hh := mul_le_mul_of_nonneg_right hη hb
  apply le_of_mul_le_mul_left (a := Mb) ?_ hMb
  change b * (1 - b) ≤ Mb * W at hvar
  nlinarith only [hh, hvar]

section Hilbert
variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

theorem refined_shared_consecutive_slacks (R P : H →L[ℝ] H)
    (hP : P.adjoint = P)
    (hinner : ∀ x : H, inner ℝ x (P x) = ‖P x‖ ^ 2)
    (hidem : ∀ x : H, P (P x) = P x)
    (hPnorm : ∀ x : H, ‖P x‖ ≤ ‖x‖)
    (hcomp : ∀ x : H, ‖R x‖ ^ 2 ≤ ‖R.adjoint x‖ ^ 2 + ‖P x‖ ^ 2)
    (u v w : H) (hv : v = R.adjoint u) (hw : w = R.adjoint v)
    (hupos : 0 < ‖u‖ ^ 2) (hvpos : 0 < ‖v‖ ^ 2)
    {omega zeta : ℝ} (homega : 0 < omega) (hzeta : 0 < zeta) :
    ‖P v‖ ^ 2 - (‖P v‖ ^ 2) ^ 2 / ‖v‖ ^ 2 ≤
      ((‖R‖ ^ 2 + 1 - ‖P v‖ ^ 2 / ‖v‖ ^ 2) / omega + 1 / zeta) *
        (omega * (‖w‖ ^ 2 + ‖P v‖ ^ 2 - ‖v‖ ^ 4 / ‖u‖ ^ 2) +
         zeta * (‖R.adjoint w‖ ^ 2 + ‖P w‖ ^ 2 - ‖w‖ ^ 4 / ‖v‖ ^ 2)) := by
  have hh := projection_variance_le_refined_shared_resource R P hP hinner hidem
    hPnorm hcomp u v w (‖v‖ ^ 2 / ‖u‖ ^ 2) (‖w‖ ^ 2 / ‖v‖ ^ 2)
    hv hw hvpos homega hzeta
  have h1 := cauchy_comparison_slack_identity R P u v w hupos hv hw
  have h2 := cauchy_comparison_slack_identity R P v w (R.adjoint w) hvpos hw rfl
  rw [hinner] at h1 h2
  have hd : 0 ≤ inner ℝ w (defect R P w) := by
    rw [defect_quadratic R P hinner]
    linarith [hcomp w]
  have hb1 : ‖P v‖ ^ 2 / ‖v‖ ^ 2 ≤ 1 := (div_le_one hvpos).mpr
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hPnorm v))
  have hcoef : 0 ≤ (‖R‖ ^ 2 + 1 - ‖P v‖ ^ 2 / ‖v‖ ^ 2) / omega + 1 / zeta := by
    have hn : 0 ≤ ‖R‖ ^ 2 + 1 - ‖P v‖ ^ 2 / ‖v‖ ^ 2 := by
      nlinarith [sq_nonneg ‖R‖]
    positivity
  have hr : omega * (‖R v - (‖v‖ ^ 2 / ‖u‖ ^ 2) • u‖ ^ 2 +
        inner ℝ v (defect R P v)) + zeta * ‖R w - (‖w‖ ^ 2 / ‖v‖ ^ 2) • v‖ ^ 2 ≤
      omega * (‖w‖ ^ 2 + ‖P v‖ ^ 2 - ‖v‖ ^ 4 / ‖u‖ ^ 2) +
        zeta * (‖R.adjoint w‖ ^ 2 + ‖P w‖ ^ 2 - ‖w‖ ^ 4 / ‖v‖ ^ 2) := by
    nlinarith [mul_nonneg hzeta.le hd]
  exact hh.trans (mul_le_mul_of_nonneg_left hr hcoef)

/-- Normalization with an arbitrary positive norm cap.  The next vector is
allowed to vanish; the corresponding normalized slack is then zero. -/
theorem refined_shared_normalized_slacks (R P : H →L[ℝ] H)
    (hP : P.adjoint = P)
    (hinner : ∀ x : H, inner ℝ x (P x) = ‖P x‖ ^ 2)
    (hidem : ∀ x : H, P (P x) = P x)
    (hPnorm : ∀ x : H, ‖P x‖ ≤ ‖x‖)
    (hcomp : ∀ x : H, ‖R x‖ ^ 2 ≤ ‖R.adjoint x‖ ^ 2 + ‖P x‖ ^ 2)
    (u v w : H) (hv : v = R.adjoint u) (hw : w = R.adjoint v)
    (hupos : 0 < ‖u‖ ^ 2) (hvpos : 0 < ‖v‖ ^ 2)
    {S omega : ℝ} (hS : 0 < S) (hR : ‖R‖ ^ 2 ≤ S) (homega : 0 < omega) (homega1 : omega < 1) :
    (‖P v‖ ^ 2 - (‖P v‖ ^ 2) ^ 2 / ‖v‖ ^ 2) / ‖v‖ ^ 2 ≤
      ((S + 1 - ‖P v‖ ^ 2 / ‖v‖ ^ 2) / omega + S / (1 - omega)) *
        (omega * ((‖w‖ ^ 2 + ‖P v‖ ^ 2 - ‖v‖ ^ 4 / ‖u‖ ^ 2) / ‖v‖ ^ 2) +
         (1 - omega) * ((‖R.adjoint w‖ ^ 2 + ‖P w‖ ^ 2 - ‖w‖ ^ 4 / ‖v‖ ^ 2) / ‖w‖ ^ 2)) := by
  let t₁ := ‖w‖ ^ 2 + ‖P v‖ ^ 2 - ‖v‖ ^ 4 / ‖u‖ ^ 2
  let t₂ := ‖R.adjoint w‖ ^ 2 + ‖P w‖ ^ 2 - ‖w‖ ^ 4 / ‖v‖ ^ 2
  have slack_nonneg (a b c : H) (ha : 0 < ‖a‖ ^ 2)
      (hb : b = R.adjoint a) (hc : c = R.adjoint b) :
      0 ≤ ‖c‖ ^ 2 + ‖P b‖ ^ 2 - ‖b‖ ^ 4 / ‖a‖ ^ 2 := by
    have hh := cauchy_comparison_slack_identity R P a b c ha hb hc
    rw [hinner] at hh
    have hd : 0 ≤ inner ℝ b (defect R P b) := by
      rw [defect_quadratic R P hinner]
      linarith [hcomp b]
    nlinarith [sq_nonneg ‖R b - (‖b‖ ^ 2 / ‖a‖ ^ 2) • a‖]
  have ht₁ : 0 ≤ t₁ := slack_nonneg u v w hupos hv hw
  have ht₂ : 0 ≤ t₂ := slack_nonneg v w (R.adjoint w) hvpos hw rfl
  have hb1 : ‖P v‖ ^ 2 / ‖v‖ ^ 2 ≤ 1 := (div_le_one hvpos).mpr
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hPnorm v))
  have hn : 0 ≤ S + 1 - ‖P v‖ ^ 2 / ‖v‖ ^ 2 := by linarith
  have hz : 0 < (1 - omega) / S := div_pos (sub_pos.mpr homega1) hS
  have hraw := refined_shared_consecutive_slacks R P hP hinner hidem hPnorm hcomp
    u v w hv hw hupos hvpos homega hz
  have hcoef : (‖R‖ ^ 2 + 1 - ‖P v‖ ^ 2 / ‖v‖ ^ 2) / omega + 1 / ((1 - omega) / S) ≤
      (S + 1 - ‖P v‖ ^ 2 / ‖v‖ ^ 2) / omega + 1 / ((1 - omega) / S) := by
    have hdiv : (‖R‖ ^ 2 + 1 - ‖P v‖ ^ 2 / ‖v‖ ^ 2) / omega ≤
        (S + 1 - ‖P v‖ ^ 2 / ‖v‖ ^ 2) / omega :=
      div_le_div_of_nonneg_right (by linarith only [hR]) homega.le
    linarith only [hdiv]
  have hres : 0 ≤ omega * t₁ + ((1 - omega) / S) * t₂ := by positivity
  have hraw' := hraw.trans (mul_le_mul_of_nonneg_right hcoef hres)
  have hnorm := pow_le_pow_left₀ (norm_nonneg _) (R.adjoint.le_opNorm v) 2
  rw [adjoint.norm_map, mul_pow, ← hw] at hnorm
  have hnorm' := hnorm.trans (mul_le_mul_of_nonneg_right hR (sq_nonneg ‖v‖))
  have hzero : ‖w‖ ^ 2 = 0 → t₂ = 0 := by
    intro hh
    have hw0 : w = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hh)
    simp [t₂, hw0]
  have hh := weighted_slack_normalize_zero hS hvpos (sq_nonneg ‖w‖) homega homega1 ht₂
    (by positivity : 0 ≤ (S + 1 - ‖P v‖ ^ 2 / ‖v‖ ^ 2) / omega + 1 / ((1 - omega) / S))
    hnorm' hzero hraw'
  have he : 1 / ((1 - omega) / S) = S / (1 - omega) := by field_simp
  rw [he] at hh
  exact hh

/-- A universal payment retaining projection geometry.  Zero and terminating
orbits, eta of either sign, and the cap boundary q=1 are all included. -/
theorem projection_observation_refined_shared_payment (R P : H →L[ℝ] H)
    (hP : P.adjoint = P)
    (hinner : ∀ x : H, inner ℝ x (P x) = ‖P x‖ ^ 2)
    (hidem : ∀ x : H, P (P x) = P x)
    (hPnorm : ∀ x : H, ‖P x‖ ≤ ‖x‖)
    (hcomp : ∀ x : H, ‖R x‖ ^ 2 ≤ ‖R.adjoint x‖ ^ 2 + ‖P x‖ ^ 2)
    (u v w : H) (hv : v = R.adjoint u) (hw : w = R.adjoint v)
    {S omega η q : ℝ} (hR : ‖R‖ ^ 2 ≤ S) (homega : 0 < omega) (homega1 : omega < 1)
    (hq : q ≤ 1) (hcap : ‖P v‖ ^ 2 ≤ q * ‖v‖ ^ 2)
    (hcoefficient : η * ((S + 1 - q) / omega + S / (1 - omega)) ≤ 1 - q) :
    η * (‖P v‖ ^ 2 / ‖v‖ ^ 2) ≤
      omega * ((‖w‖ ^ 2 + ‖P v‖ ^ 2 - ‖v‖ ^ 4 / ‖u‖ ^ 2) / ‖v‖ ^ 2) +
      (1 - omega) * ((‖R.adjoint w‖ ^ 2 + ‖P w‖ ^ 2 - ‖w‖ ^ 4 / ‖v‖ ^ 2) / ‖w‖ ^ 2) := by
  by_cases hv0 : v = 0
  · have hw0 : w = 0 := by simp [hw, hv0]
    simp [hv0, hw0]
  have hvpos : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv0)
  have hvbound := pow_le_pow_left₀ (norm_nonneg _) (R.adjoint.le_opNorm u) 2
  rw [adjoint.norm_map, mul_pow, ← hv] at hvbound
  have hvbound' := hvbound.trans (mul_le_mul_of_nonneg_right hR (sq_nonneg ‖u‖))
  have hS : 0 < S := by nlinarith [sq_nonneg ‖u‖]
  have hupos : 0 < ‖u‖ ^ 2 := by nlinarith [sq_nonneg ‖u‖]
  have hb : 0 ≤ ‖P v‖ ^ 2 / ‖v‖ ^ 2 := by positivity
  have hbq : ‖P v‖ ^ 2 / ‖v‖ ^ 2 ≤ q := (div_le_iff₀ hvpos).mpr hcap
  have hvar := refined_shared_normalized_slacks R P hP hinner hidem hPnorm hcomp
    u v w hv hw hupos hvpos hS hR homega homega1
  have he : (‖P v‖ ^ 2 - (‖P v‖ ^ 2) ^ 2 / ‖v‖ ^ 2) / ‖v‖ ^ 2 =
      (‖P v‖ ^ 2 / ‖v‖ ^ 2) * (1 - ‖P v‖ ^ 2 / ‖v‖ ^ 2) := by ring
  rw [he] at hvar
  exact payment_of_refined_variance hS homega homega1 hb hbq hq hvar hcoefficient

end Hilbert

variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ),
    κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
  (hμ : admissibleMeasure (potentialMeasure φ))

/-- Actual-law wrapper.  Only the existing first-observation cap is used;
the extra scalar condition q<=1 records the useful cap range explicitly. -/
theorem actual_projection_observation_refined_shared_payment
    (u v w : GradedCenteredTensorHilbert hφ)
    (hv : v = (gradedTensorIntegration hφ hκ hlower).adjoint u)
    (hw : w = (gradedTensorIntegration hφ hκ hlower).adjoint v)
    {S weight η K l : ℝ}
    (hR : ‖gradedTensorIntegration hφ hκ hlower‖ ^ 2 ≤ S)
    (hweight : 0 < weight) (hweight1 : weight < 1) (hKl : 0 < K * l)
    (hq : 2 / (K * l) ≤ 1) (hl : K * l * ‖u‖ ^ 2 ≤ ‖v‖ ^ 2)
    (hcoefficient : η * ((S + 1 - 2 / (K * l)) / weight +
      S / (1 - weight)) ≤ 1 - 2 / (K * l)) :
    let R := gradedTensorIntegration hφ hκ hlower
    let P := gradedLinearTensorProjection hφ hκ hlower hμ.isotropic
    η * (‖P v‖ ^ 2 / ‖v‖ ^ 2) ≤
      weight * ((‖w‖ ^ 2 + ‖P v‖ ^ 2 - ‖v‖ ^ 4 / ‖u‖ ^ 2) / ‖v‖ ^ 2) +
      (1 - weight) * ((‖R.adjoint w‖ ^ 2 + ‖P w‖ ^ 2 -
        ‖w‖ ^ 4 / ‖v‖ ^ 2) / ‖w‖ ^ 2) := by
  have hobs := actual_first_graded_observation_sq_le hφ hκ hlower hμ u
  simp only [pow_one] at hobs
  rw [← hv, ← gradedLinearTensorProjection_norm hφ hκ hlower hμ.isotropic] at hobs
  have hcap : ‖gradedLinearTensorProjection hφ hκ hlower hμ.isotropic v‖ ^ 2 ≤
      (2 / (K * l)) * ‖v‖ ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2 / (K * l))
    have he : (2 / (K * l)) * (K * l * ‖u‖ ^ 2) = 2 * ‖u‖ ^ 2 := by
      calc
        _ = ((2 / (K * l)) * (K * l)) * ‖u‖ ^ 2 := by ring
        _ = 2 * ‖u‖ ^ 2 := by rw [div_mul_cancel₀ _ hKl.ne']
    rw [he] at hh
    exact hobs.trans hh
  exact projection_observation_refined_shared_payment
    (gradedTensorIntegration hφ hκ hlower)
    (gradedLinearTensorProjection hφ hκ hlower hμ.isotropic)
    (gradedLinearTensorProjection_adjoint hφ hκ hlower hμ.isotropic)
    (gradedLinearTensorProjection_inner hφ hκ hlower hμ.isotropic)
    (gradedLinearTensorProjection_idempotent hφ hκ hlower hμ.isotropic)
    (gradedLinearTensorProjection_norm_le hφ hκ hlower hμ.isotropic)
    (actual_graded_linear_projection_comparison hφ hκ hlower hμ.isotropic)
    u v w hv hw hR hweight hweight1 hq hcap hcoefficient

end KLSConstantImprovement.ProjectionGeometryPayment

#print axioms KLSConstantImprovement.ProjectionGeometryPayment.weighted_slack_normalize_zero
#print axioms KLSConstantImprovement.ProjectionGeometryPayment.payment_of_refined_variance
#print axioms KLSConstantImprovement.ProjectionGeometryPayment.refined_shared_consecutive_slacks
#print axioms KLSConstantImprovement.ProjectionGeometryPayment.refined_shared_normalized_slacks
#print axioms KLSConstantImprovement.ProjectionGeometryPayment.projection_observation_refined_shared_payment
#print axioms KLSConstantImprovement.ProjectionGeometryPayment.actual_projection_observation_refined_shared_payment

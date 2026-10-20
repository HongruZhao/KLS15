import KLSConstantImprovement.PositiveFiniteHeadBellman

/-! The quadratic observation cap supplies a conservative affine lower
transition, and exact square identities supply each finite Bellman stage. -/
noncomputable section
namespace KLSConstantImprovement.QuadraticCapBellmanCertificates
open KLSConstantImprovement.PositiveFiniteHeadBellman
set_option maxHeartbeats 2000000

def capChord (A R r : ℝ) : ℝ := (1+A/R)*r-A*(1+1/R)

theorem capChord_le_self {A R r : ℝ} (hA : 0 ≤ A) (hR : 0<R)
    (hr : r ≤ R) : capChord A R r ≤ r := by
  have he : r-capChord A R r=A*(R+1-r)/R := by
    unfold capChord
    field_simp [ne_of_gt hR] <;> ring
  have hn : 0 ≤ A*(R+1-r)/R :=
    div_nonneg (mul_nonneg hA (by linarith)) hR.le
  rw [←he] at hn
  linarith

theorem capChord_le_quadratic_transition {A R r : ℝ}
    (hA : 0 ≤ A) (hR : 0<R) (hr : 1 ≤ r) (hrR : r ≤ R) :
    capChord A R r ≤ r-A/r := by
  have hr0 : 0<r := by linarith
  have he : r-A/r-capChord A R r=A*(r-1)*(R-r)/(R*r) := by
    unfold capChord
    field_simp [ne_of_gt hR,ne_of_gt hr0] <;> ring
  have hn : 0 ≤ A*(r-1)*(R-r)/(R*r) :=
    div_nonneg (mul_nonneg (mul_nonneg hA (by linarith)) (by linarith))
      (mul_pos hR hr0).le
  rw [←he] at hn
  linarith

theorem transition_payment_of_quadratic_cap {A R w : ℝ}
    {current next : Affine}
    (h : StageCertificate w R (capChord A R) current next)
    (hA : 0 ≤ A) (hR : 0<R)
    {z r s d : ℝ} (hz : 0 ≤ z) (hr : 1 ≤ r) (hs : 0 ≤ s)
    (hd : 0 ≤ d) (hrR : r ≤ R) (hdrop : r-s ≤ d) (hcap : d ≤ A/r) :
    z*current.positive r ≤ w*(z*d)+(z*s)*next.positive s := by
  have hlr := capChord_le_self hA hR hrR
  have hls : capChord A R r ≤ s :=
    (capChord_le_quadratic_transition hA hR hr hrR).trans (by linarith)
  exact transition_payment h hz (by linarith) hs hd hrR hdrop hlr hls

/-- A rational quadratic identity with a nonnegative domain multiplier
is enough to prove the entire stage, including its positive part. -/
theorem stage_certificate_of_square_identity {w R : ℝ} {lower : ℝ → ℝ}
    {current next : Affine} {contact multiplier : ℝ} (q : ℝ → ℝ → ℝ)
    (hw : 0 ≤ w) (hc : 0 ≤ current.slope) (hn : 0 ≤ next.slope)
    (hc1 : current.eval 1 ≤ 0) (hn1 : next.eval 1 ≤ 0)
    (hm : 0 ≤ multiplier)
    (hid : ∀ r s, w*(r-s)+s*next.eval s-current.eval r=
      next.slope*(s-contact)^2+multiplier*q r s)
    (hq : ∀ r, 1 ≤ r → r ≤ R → ∀ s,
      1 ≤ s → lower r ≤ s → s ≤ r → 0 ≤ q r s) :
    StageCertificate w R lower current next := by
  refine ⟨hw,hc,hn,hc1,hn1,?_⟩
  intro r hr hrR s hs hls hsr
  have hp := add_nonneg (mul_nonneg hn (sq_nonneg (s-contact)))
    (mul_nonneg hm (hq r hr hrR s hs hls hsr))
  rw [←hid r s] at hp
  have he : current.eval r ≤ w*(r-s)+s*next.eval s := by linarith
  exact he.trans (add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left (le_max_right 0 (next.eval s)) (by linarith)))

end KLSConstantImprovement.QuadraticCapBellmanCertificates
#print axioms KLSConstantImprovement.QuadraticCapBellmanCertificates.capChord_le_quadratic_transition
#print axioms KLSConstantImprovement.QuadraticCapBellmanCertificates.transition_payment_of_quadratic_cap
#print axioms KLSConstantImprovement.QuadraticCapBellmanCertificates.stage_certificate_of_square_identity

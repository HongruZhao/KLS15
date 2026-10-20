import KLSConstantImprovement.RoundedAffineBellman

/-! Exact quadratic-cap affine Bellman certificates. The two-variable
sum of squares retains r*s >= r^2-A instead of replacing it by a chord.
Every coefficient and domain condition is explicit. -/
noncomputable section
namespace KLSConstantImprovement.ExactQuadraticCapBellmanCertificates
open KLSConstantImprovement.PositiveFiniteHeadBellman
set_option maxHeartbeats 2000000

def cap (A r : ℝ) : ℝ := r-A/r

theorem quadratic_support_identity (A a b w r0 s0 μ r s : ℝ)
    (hcap : r0*s0=r0^2-A) (hstation : 2*a*s0+b-w=μ*r0) :
    w*(r-s)+s*(a*s+b)-
      ((w+μ*(2*r0-s0))*r+(-a*s0^2-2*μ*A))=
    (a-μ/4)*(s-s0)^2+μ*(r-r0-(s-s0)/2)^2+
      μ*(r*s-r^2+A) := by
  have hb : b=w+μ*r0-2*a*s0 := by linarith
  have hA : A=r0^2-r0*s0 := by linarith
  rw [hb,hA]
  ring

theorem stage_certificate_of_quadratic_identity
    {A w R μ : ℝ} {current next : Affine} {r0 s0 : ℝ}
    (hw : 0 ≤ w) (hc : 0 ≤ current.slope) (hn : 0 ≤ next.slope)
    (hc1 : current.eval 1 ≤ 0) (hn1 : next.eval 1 ≤ 0)
    (hm : 0 ≤ μ) (hpsd : μ ≤ 4*next.slope)
    (hid : ∀ r s,w*(r-s)+s*next.eval s-current.eval r=
      (next.slope-μ/4)*(s-s0)^2+μ*(r-r0-(s-s0)/2)^2+
        μ*(r*s-r^2+A)) :
    StageCertificate w R (cap A) current next := by
  refine ⟨hw,hc,hn,hc1,hn1,?_⟩
  intro r hr hrR s hs hls hsr
  have hr0 : 0 < r := by linarith
  have hactual : 0 ≤ r*s-r^2+A := by
    have hh := mul_le_mul_of_nonneg_left hls hr0.le
    dsimp only [cap] at hh
    have he : r*(r-A/r)=r^2-A := by
      field_simp [ne_of_gt hr0] <;> ring
    rw [he] at hh
    nlinarith
  have hp := add_nonneg
    (add_nonneg (mul_nonneg (by linarith : 0 ≤ next.slope-μ/4) (sq_nonneg (s-s0)))
      (mul_nonneg hm (sq_nonneg (r-r0-(s-s0)/2)))) (mul_nonneg hm hactual)
  rw [←hid r s] at hp
  have he : current.eval r ≤ w*(r-s)+s*next.eval s := by linarith
  exact he.trans (add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left (le_max_right 0 (next.eval s)) (by linarith)))

theorem transition_payment_of_exact_cap {A R w : ℝ}
    {current next : Affine}
    (h : StageCertificate w R (cap A) current next) (hA : 0 ≤ A)
    {z r s d : ℝ} (hz : 0 ≤ z) (hr : 1 ≤ r) (hs : 0 ≤ s)
    (hd : 0 ≤ d) (hrR : r ≤ R) (hdrop : r-s ≤ d) (hcap : d ≤ A/r) :
    z*current.positive r ≤ w*(z*d)+(z*s)*next.positive s := by
  have hr0 : 0 < r := by linarith
  have hlr : cap A r ≤ r := by
    dsimp only [cap]
    exact sub_le_self _ (div_nonneg hA hr0.le)
  have hls : cap A r ≤ s := by dsimp only [cap];linarith
  exact transition_payment h hz (by linarith) hs hd hrR hdrop hlr hls

end KLSConstantImprovement.ExactQuadraticCapBellmanCertificates
#print axioms KLSConstantImprovement.ExactQuadraticCapBellmanCertificates.quadratic_support_identity
#print axioms KLSConstantImprovement.ExactQuadraticCapBellmanCertificates.stage_certificate_of_quadratic_identity
#print axioms KLSConstantImprovement.ExactQuadraticCapBellmanCertificates.transition_payment_of_exact_cap

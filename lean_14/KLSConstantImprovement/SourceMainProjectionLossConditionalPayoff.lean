import KLSConstantImprovement.SourceRetainedLossResponseConditionalPayoff

/-! Retain the MAIN scalar graph projection loss D_B, distinct from the
response matching/target curvature and the source affine frontier charge.
Actual same-graph/Riesz/source bindings are explicit paper inputs. The new
response and production allowances remain OPEN on actual laws. -/
noncomputable section
namespace KLSConstantImprovement.SourceMainProjectionLossConditionalPayoff
open SourceMatchedMeanResponseConditionalPayoff
open SourceRetainedLossResponseConditionalPayoff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem main_projection_young_credit (a f : E) {V J D : ℝ}
    (hvariance : V=9*‖a+f‖^2) (hprojection : ‖a‖^2+D=J) :
    V ≤ (99/7:ℝ)*J+(99/4:ℝ)*‖f‖^2-(99/7:ℝ)*D := by
  have h := source_split_four_sevenths_young a f
  nlinarith

theorem main_loss_widened_response_gives_raw335_half (a f : E)
    {V J D N r s g W p rem q : ℝ} (hneff : 0 ≤ N-g/2)
    (hvariance : V=9*‖a+f‖^2) (hprojection : ‖a‖^2+D=J)
    (hdisk : (r-(N-g/2))^2+s^2 ≤ (N-g/2)^2)
    (hcomp : W+2*p+2*rem=3*(r+s))
    (hmain : J+Real.sqrt 2*q/2 ≤ (1+Real.sqrt 2)*W)
    (hresponse : ‖f‖^2 ≤ 2*r+(27/4:ℝ)*g+
      (8/7:ℝ)*(1+Real.sqrt 2)*(p+rem)+(2/7:ℝ)*Real.sqrt 2*q+(4/7:ℝ)*D) :
    V ≤ (671/2:ℝ)*N-(11/16:ℝ)*g := by
  let B : ℝ := (33/7:ℝ)*(1+Real.sqrt 2)
  let A : ℝ := B+11/2
  have hcert : 0 ≤ (671/18:ℝ)-A ∧ A^2+B^2 ≤ ((671/18:ℝ)-A)^2 :=
    widened_loss_coefficient_certificate
  have hs := disk_linear_support hneff hcert.1 hcert.2 hdisk
  have hy := main_projection_young_credit a f hvariance hprojection
  have hw : W=3*(r+s)-2*p-2*rem := by linarith
  rw [hw] at hmain
  have hv : V ≤ 9*(A*r+B*s)+(2673/16:ℝ)*g := by
    dsimp [A,B]
    nlinarith
  nlinarith

theorem main_loss_widened_response_gives_raw336 (a f : E)
    {V J D N r s g W p rem q : ℝ} (hneff : 0 ≤ N-g/2) (hg : 0 ≤ g)
    (hvariance : V=9*‖a+f‖^2) (hprojection : ‖a‖^2+D=J)
    (hdisk : (r-(N-g/2))^2+s^2 ≤ (N-g/2)^2)
    (hcomp : W+2*p+2*rem=3*(r+s))
    (hmain : J+Real.sqrt 2*q/2 ≤ (1+Real.sqrt 2)*W)
    (hresponse : ‖f‖^2 ≤ 2*r+(27/4:ℝ)*g+
      (8/7:ℝ)*(1+Real.sqrt 2)*(p+rem)+(2/7:ℝ)*Real.sqrt 2*q+(4/7:ℝ)*D) :
    V ≤ 336*N := by
  have h := main_loss_widened_response_gives_raw335_half a f hneff
    hvariance hprojection hdisk hcomp hmain hresponse
  linarith

theorem main_loss_half_response_gives_raw333 (a f : E)
    {V J D N r s g W p rem q : ℝ} (hneff : 0 ≤ N-g/2)
    (hvariance : V=9*‖a+f‖^2) (hprojection : ‖a‖^2+D=J)
    (hdisk : (r-(N-g/2))^2+s^2 ≤ (N-g/2)^2)
    (hcomp : W+2*p+2*rem=3*(r+s))
    (hmain : J+Real.sqrt 2*q/2 ≤ (1+Real.sqrt 2)*W)
    (hresponse : ‖f‖^2 ≤ 2*r+6*g+(1+Real.sqrt 2)*(p+rem)+Real.sqrt 2*q/4+D/2) :
    V ≤ 333*N-(9/2:ℝ)*g := by
  let B : ℝ := (9/2:ℝ)*(1+Real.sqrt 2)
  let A : ℝ := B+6
  have hcert : 0 ≤ 37-A ∧ A^2+B^2 ≤ (37-A)^2 := matched_mean_coefficient_certificate
  have hs := disk_linear_support hneff hcert.1 hcert.2 hdisk
  have hy := source_split_half_young a f
  have hw : W=3*(r+s)-2*p-2*rem := by linarith
  rw [hw] at hmain
  have hv : V ≤ 9*(A*r+B*s)+162*g := by
    dsimp [A,B]
    nlinarith
  nlinarith

theorem main_loss_production_payment_implies_response
    {I W r rho xi losses D g k q : ℝ}
    (hShifted : I ≤ W+r+rho-xi/2-losses)
    (hPaid : xi/2+losses+(4/7:ℝ)*D ≥ W-r+rho-(27/4:ℝ)*g-
      (8/7:ℝ)*(1+Real.sqrt 2)*k-(2/7:ℝ)*Real.sqrt 2*q) :
    I ≤ 2*r+(27/4:ℝ)*g+(8/7:ℝ)*(1+Real.sqrt 2)*k+
      (2/7:ℝ)*Real.sqrt 2*q+(4/7:ℝ)*D := by
  linarith

end KLSConstantImprovement.SourceMainProjectionLossConditionalPayoff
#print axioms KLSConstantImprovement.SourceMainProjectionLossConditionalPayoff.main_projection_young_credit
#print axioms KLSConstantImprovement.SourceMainProjectionLossConditionalPayoff.main_loss_widened_response_gives_raw335_half
#print axioms KLSConstantImprovement.SourceMainProjectionLossConditionalPayoff.main_loss_widened_response_gives_raw336
#print axioms KLSConstantImprovement.SourceMainProjectionLossConditionalPayoff.main_loss_half_response_gives_raw333
#print axioms KLSConstantImprovement.SourceMainProjectionLossConditionalPayoff.main_loss_production_payment_implies_response

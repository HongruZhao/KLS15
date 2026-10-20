import KLSConstantImprovement.SourceGramGapResponseConditionalPayoff

/-! Retain the paid direct p3/R3 and distinct affine q discounts in the
matched source-response payoff. Every response budget below is OPEN on
actual laws. This proves conditional implications, no new universal CP. -/
noncomputable section
namespace KLSConstantImprovement.SourceRetainedLossResponseConditionalPayoff
open SourceMatchedMeanResponseConditionalPayoff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem retained_losses_response_gives_raw333 (a f : E)
    {V J N r s g W p rem q : ℝ} (hneff : 0 ≤ N-g/2)
    (hvariance : V=9*‖a+f‖^2) (hprojection : ‖a‖^2 ≤ J)
    (hdisk : (r-(N-g/2))^2+s^2 ≤ (N-g/2)^2)
    (hcomp : W+2*p+2*rem=3*(r+s))
    (hmain : J+Real.sqrt 2*q/2 ≤ (1+Real.sqrt 2)*W)
    (hresponse : ‖f‖^2 ≤ 2*r+6*g+(1+Real.sqrt 2)*(p+rem)+Real.sqrt 2*q/4) :
    V ≤ 333*N-(9/2:ℝ)*g := by
  let B : ℝ := (9/2:ℝ)*(1+Real.sqrt 2)
  let A : ℝ := B+6
  have hcert : 0 ≤ 37-A ∧ A^2+B^2 ≤ (37-A)^2 :=
    matched_mean_coefficient_certificate
  have hs := disk_linear_support hneff hcert.1 hcert.2 hdisk
  have hy := source_split_half_young a f
  have hw : W=3*(r+s)-2*p-2*rem := by linarith
  rw [hw] at hmain
  have hv : V ≤ 9*(A*r+B*s)+162*g := by
    dsimp [A,B]
    nlinarith
  nlinarith

theorem source_split_four_sevenths_young (a f : E) :
    9*‖a+f‖^2 ≤ (99/7:ℝ)*‖a‖^2+(99/4:ℝ)*‖f‖^2 := by
  have hc : inner ℝ a f ≤ ‖a‖*‖f‖ :=
    (le_abs_self _).trans (abs_real_inner_le_norm _ _)
  have hy := sq_nonneg (4*‖a‖-7*‖f‖)
  rw [norm_add_sq_real]
  nlinarith

theorem widened_loss_coefficient_certificate :
    0 ≤ (671/18:ℝ)-((33/7:ℝ)*(1+Real.sqrt 2)+11/2) ∧
    ((33/7:ℝ)*(1+Real.sqrt 2)+11/2)^2+((33/7:ℝ)*(1+Real.sqrt 2))^2 ≤
      ((671/18:ℝ)-((33/7:ℝ)*(1+Real.sqrt 2)+11/2))^2 := by
  have hp := Real.sqrt_nonneg (2:ℝ)
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hu : Real.sqrt (2:ℝ) ≤ 99/70 := by nlinarith
  constructor <;> nlinarith

theorem widened_retained_losses_response_gives_raw335_half (a f : E)
    {V J N r s g W p rem q : ℝ} (hneff : 0 ≤ N-g/2)
    (hvariance : V=9*‖a+f‖^2) (hprojection : ‖a‖^2 ≤ J)
    (hdisk : (r-(N-g/2))^2+s^2 ≤ (N-g/2)^2)
    (hcomp : W+2*p+2*rem=3*(r+s))
    (hmain : J+Real.sqrt 2*q/2 ≤ (1+Real.sqrt 2)*W)
    (hresponse : ‖f‖^2 ≤ 2*r+(27/4:ℝ)*g+
      (8/7:ℝ)*(1+Real.sqrt 2)*(p+rem)+(2/7:ℝ)*Real.sqrt 2*q) :
    V ≤ (671/2:ℝ)*N-(11/16:ℝ)*g := by
  let B : ℝ := (33/7:ℝ)*(1+Real.sqrt 2)
  let A : ℝ := B+11/2
  have hcert : 0 ≤ (671/18:ℝ)-A ∧ A^2+B^2 ≤ ((671/18:ℝ)-A)^2 :=
    widened_loss_coefficient_certificate
  have hs := disk_linear_support hneff hcert.1 hcert.2 hdisk
  have hy := source_split_four_sevenths_young a f
  have hw : W=3*(r+s)-2*p-2*rem := by linarith
  rw [hw] at hmain
  have hv : V ≤ 9*(A*r+B*s)+(2673/16:ℝ)*g := by
    dsimp [A,B]
    nlinarith
  nlinarith

theorem widened_retained_losses_response_gives_raw336 (a f : E)
    {V J N r s g W p rem q : ℝ} (hneff : 0 ≤ N-g/2) (hg : 0 ≤ g)
    (hvariance : V=9*‖a+f‖^2) (hprojection : ‖a‖^2 ≤ J)
    (hdisk : (r-(N-g/2))^2+s^2 ≤ (N-g/2)^2)
    (hcomp : W+2*p+2*rem=3*(r+s))
    (hmain : J+Real.sqrt 2*q/2 ≤ (1+Real.sqrt 2)*W)
    (hresponse : ‖f‖^2 ≤ 2*r+(27/4:ℝ)*g+
      (8/7:ℝ)*(1+Real.sqrt 2)*(p+rem)+(2/7:ℝ)*Real.sqrt 2*q) : V ≤ 336*N := by
  have h := widened_retained_losses_response_gives_raw335_half a f hneff
    hvariance hprojection hdisk hcomp hmain hresponse
  linarith

end KLSConstantImprovement.SourceRetainedLossResponseConditionalPayoff

#print axioms KLSConstantImprovement.SourceRetainedLossResponseConditionalPayoff.retained_losses_response_gives_raw333
#print axioms KLSConstantImprovement.SourceRetainedLossResponseConditionalPayoff.source_split_four_sevenths_young
#print axioms KLSConstantImprovement.SourceRetainedLossResponseConditionalPayoff.widened_loss_coefficient_certificate
#print axioms KLSConstantImprovement.SourceRetainedLossResponseConditionalPayoff.widened_retained_losses_response_gives_raw335_half
#print axioms KLSConstantImprovement.SourceRetainedLossResponseConditionalPayoff.widened_retained_losses_response_gives_raw336

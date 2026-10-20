import KLSConstantImprovement.TensorGramQuarticSourceDeficit
import KLSConstantImprovement.SourceThirdAdjointResponse

/-! Retaining the matched source mean broadens the sufficient response gate.
The numerical same-response estimate I_e <= 2r is OPEN. The source fields,
matched disk and main identification remain explicit; no universal raw or
Poincare bound is asserted. -/
noncomputable section
namespace KLSConstantImprovement.SourceMatchedMeanResponseConditionalPayoff

theorem disk_linear_support {A B cap N r s : ℝ}
    (hN : 0 ≤ N) (hcap : 0 ≤ cap-A)
    (hcoef : A^2+B^2 ≤ (cap-A)^2)
    (hdisk : (r-N)^2+s^2 ≤ N^2) :
    A*r+B*s ≤ cap*N := by
  have hid : (A*(r-N)+B*s)^2+(B*(r-N)-A*s)^2 =
      (A^2+B^2)*((r-N)^2+s^2) := by ring
  have hsq : (A*(r-N)+B*s)^2 ≤ ((cap-A)*N)^2 := by
    calc
      _ ≤ (A^2+B^2)*((r-N)^2+s^2) := by
        rw [← hid]
        exact le_add_of_nonneg_right (sq_nonneg _)
      _ ≤ (A^2+B^2)*N^2 :=
        mul_le_mul_of_nonneg_left hdisk (add_nonneg (sq_nonneg _) (sq_nonneg _))
      _ ≤ (cap-A)^2*N^2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg N)
      _ = ((cap-A)*N)^2 := by ring
  have hlin := le_of_sq_le_sq hsq (mul_nonneg hcap hN)
  nlinarith

theorem matched_mean_coefficient_certificate :
    0 ≤ 37-((9/2:ℝ)*(1+Real.sqrt 2)+6) ∧
    ((9/2:ℝ)*(1+Real.sqrt 2)+6)^2+((9/2:ℝ)*(1+Real.sqrt 2))^2 ≤
      (37-((9/2:ℝ)*(1+Real.sqrt 2)+6))^2 := by
  have hp := Real.sqrt_nonneg (2:ℝ)
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hu : Real.sqrt (2:ℝ) ≤ 71/50 := by nlinarith
  constructor <;> nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem source_split_half_young (a f : E) :
    9*‖a+f‖^2 ≤ (27/2:ℝ)*‖a‖^2+27*‖f‖^2 := by
  have hc : inner ℝ a f ≤ ‖a‖*‖f‖ :=
    (le_abs_self _).trans (abs_real_inner_le_norm _ _)
  have hy := sq_nonneg (‖a‖-2*‖f‖)
  rw [norm_add_sq_real]
  nlinarith

theorem matched_response_double_mean_gives_raw333 (a f : E)
    {V J N r s : ℝ} (hN : 0 ≤ N)
    (hvariance : V = 9*‖a+f‖^2)
    (hprojection : ‖a‖^2 ≤ J)
    (hdisk : (r-N)^2+s^2 ≤ N^2)
    (hmain : J ≤ 3*(1+Real.sqrt 2)*(r+s))
    (hresponse : ‖f‖^2 ≤ 2*r) : V ≤ 333*N := by
  let B : ℝ := (9/2:ℝ)*(1+Real.sqrt 2)
  let A : ℝ := B+6
  have hcert : 0 ≤ 37-A ∧ A^2+B^2 ≤ (37-A)^2 :=
    matched_mean_coefficient_certificate
  have hsupport := disk_linear_support hN hcert.1 hcert.2 hdisk
  have hy := source_split_half_young a f
  have hv : V ≤ 9*(A*r+B*s) := by
    dsimp [A,B]
    nlinarith
  nlinarith

theorem matched_response_double_mean_gives_raw336 (a f : E)
    {V J N r s : ℝ} (hN : 0 ≤ N)
    (hvariance : V = 9*‖a+f‖^2)
    (hprojection : ‖a‖^2 ≤ J)
    (hdisk : (r-N)^2+s^2 ≤ N^2)
    (hmain : J ≤ 3*(1+Real.sqrt 2)*(r+s))
    (hresponse : ‖f‖^2 ≤ 2*r) : V ≤ 336*N := by
  have h := matched_response_double_mean_gives_raw333 a f hN
    hvariance hprojection hdisk hmain hresponse
  linarith

end KLSConstantImprovement.SourceMatchedMeanResponseConditionalPayoff
#print axioms KLSConstantImprovement.SourceMatchedMeanResponseConditionalPayoff.disk_linear_support
#print axioms KLSConstantImprovement.SourceMatchedMeanResponseConditionalPayoff.matched_mean_coefficient_certificate
#print axioms KLSConstantImprovement.SourceMatchedMeanResponseConditionalPayoff.source_split_half_young
#print axioms KLSConstantImprovement.SourceMatchedMeanResponseConditionalPayoff.matched_response_double_mean_gives_raw333
#print axioms KLSConstantImprovement.SourceMatchedMeanResponseConditionalPayoff.matched_response_double_mean_gives_raw336

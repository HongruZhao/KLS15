import KLSConstantImprovement.SourceMatchedMeanResponseConditionalPayoff

/-! The stronger matched disk keeps its Gram-half orientation gap.
Actual `g = Lambda(Qhalf,Qhalf)-r = delta_T-delta_D` and the same
source/Riesz/main identities remain analytic inputs. The widened numerical
response budget is OPEN. This does not prove a universal raw or CP bound,
and does not spend the distinct affine, curvature or rotation charges. -/
noncomputable section
namespace KLSConstantImprovement.SourceGramGapResponseConditionalPayoff
open SourceMatchedMeanResponseConditionalPayoff

theorem matched_disk_retains_gram_gap {N r delta g s : ℝ}
    (hr : 0 ≤ r) (hdelta : 0 ≤ delta)
    (hrel : delta = 2*N-r-g) (hcross : s^2 ≤ r*delta) :
    0 ≤ N-g/2 ∧ (r-(N-g/2))^2+s^2 ≤ (N-g/2)^2 := by
  constructor
  · linarith
  · rw [hrel] at hcross
    nlinarith

theorem weighted_cost_with_gram_credit_gives_response {I C qrot U r g : ℝ}
    (hresponse : I ≤ C-qrot) (hcost : C-qrot ≤ r+U+6*g)
    (hquadratic : U ≤ r) : I ≤ 2*r+6*g := by linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem gram_gap_response_gives_raw333_with_margin (a f : E)
    {V J N r s g : ℝ} (hneff : 0 ≤ N-g/2)
    (hvariance : V = 9*‖a+f‖^2) (hprojection : ‖a‖^2 ≤ J)
    (hdisk : (r-(N-g/2))^2+s^2 ≤ (N-g/2)^2)
    (hmain : J ≤ 3*(1+Real.sqrt 2)*(r+s))
    (hresponse : ‖f‖^2 ≤ 2*r+6*g) :
    V ≤ 333*N-(9/2:ℝ)*g := by
  let B : ℝ := (9/2:ℝ)*(1+Real.sqrt 2)
  let A : ℝ := B+6
  have hcert : 0 ≤ 37-A ∧ A^2+B^2 ≤ (37-A)^2 :=
    matched_mean_coefficient_certificate
  have hs := disk_linear_support hneff hcert.1 hcert.2 hdisk
  have hy := source_split_half_young a f
  have hv : V ≤ 9*(A*r+B*s)+162*g := by
    dsimp [A,B]
    nlinarith
  nlinarith

theorem gram_gap_response_gives_raw336 (a f : E)
    {V J N r s g : ℝ} (hneff : 0 ≤ N-g/2) (hg : 0 ≤ g)
    (hvariance : V = 9*‖a+f‖^2) (hprojection : ‖a‖^2 ≤ J)
    (hdisk : (r-(N-g/2))^2+s^2 ≤ (N-g/2)^2)
    (hmain : J ≤ 3*(1+Real.sqrt 2)*(r+s))
    (hresponse : ‖f‖^2 ≤ 2*r+6*g) : V ≤ 336*N := by
  have h := gram_gap_response_gives_raw333_with_margin a f hneff
    hvariance hprojection hdisk hmain hresponse
  linarith

end KLSConstantImprovement.SourceGramGapResponseConditionalPayoff
#print axioms KLSConstantImprovement.SourceGramGapResponseConditionalPayoff.matched_disk_retains_gram_gap
#print axioms KLSConstantImprovement.SourceGramGapResponseConditionalPayoff.weighted_cost_with_gram_credit_gives_response
#print axioms KLSConstantImprovement.SourceGramGapResponseConditionalPayoff.gram_gap_response_gives_raw333_with_margin
#print axioms KLSConstantImprovement.SourceGramGapResponseConditionalPayoff.gram_gap_response_gives_raw336

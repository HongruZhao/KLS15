import KLSConstantImprovement.ActualDeficitBesselBound
import KLSConstantImprovement.OriginalSourceLinearResponseSlack

/-! Same-original-law Bessel refinement of the linear source response.
The exact q_K/4 component identity remains explicit. Its covariance slack
is split into the fourth deficit and a nonnegative Bessel remainder;
they are not spent separately from the unsplit slot slack. The signed
nonlinear response completion is still an open numerical premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
namespace KLSConstantImprovement.ActualLinearResponseBesselSlack
open KLS KLSBelow25.CubicSymmetricNoise
open ActualDeficitTensorBounds ActualDeficitBesselBound
variable {n : ℕ}

theorem original_bessel_remaining_nonneg {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n)) :
    0 ≤ 8 * tensorSquare T - sliceDeficit μ T - annihilationSquare μ T := by
  have hb := annihilationSquare_le_fourth_add_two hμ T
  unfold sliceDeficit
  linarith

theorem exact_actual_linear_slack {μ : Measure (Space n)}
    (T : Array3 (Fin n)) {Ilin dK : ℝ}
    (hcomponent : Ilin = (annihilationSquare μ T + signedTraceSquare μ T)/4-dK/16) :
    (10/3 : ℝ) * tensorSquare T - Ilin =
      dK/16 + sliceDeficit μ T/4 +
      (8 * tensorSquare T-sliceDeficit μ T-annihilationSquare μ T)/4 +
      ((16/3 : ℝ) * tensorSquare T-signedTraceSquare μ T)/4 := by
  rw [hcomponent]
  ring

theorem actual_linear_response_cap_with_deficits {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ i j k, T i j k = T j i k)
    (hT23 : ∀ i j k, T i j k = T i k j) {Ilin dK : ℝ}
    (hcomponent : Ilin = (annihilationSquare μ T + signedTraceSquare μ T)/4-dK/16) :
    Ilin ≤ (10/3 : ℝ) * tensorSquare T-sliceDeficit μ T/4-dK/16 := by
  have hb := original_bessel_remaining_nonneg hμ T
  have hs := signedTraceSquare_le_sixteen_thirds hμ T hT12 hT23
  have he := exact_actual_linear_slack T hcomponent
  linarith

theorem actual_seven_halves_response_completion {μ : Measure (Space n)}
    (T : Array3 (Fin n)) {Ilin dK cross IY Itotal : ℝ}
    (hcomponent : Ilin = (annihilationSquare μ T + signedTraceSquare μ T)/4-dK/16)
    (hsplit : Itotal = Ilin + 2 * cross + IY)
    (hcorrection : 2 * cross + IY ≤ tensorSquare T/6 + dK/16 +
      sliceDeficit μ T/4 +
      (8 * tensorSquare T-sliceDeficit μ T-annihilationSquare μ T)/4 +
      ((16/3 : ℝ) * tensorSquare T-signedTraceSquare μ T)/4) :
    Itotal ≤ (7/2 : ℝ) * tensorSquare T := by
  have he := exact_actual_linear_slack T hcomponent
  linarith

end KLSConstantImprovement.ActualLinearResponseBesselSlack
#print axioms KLSConstantImprovement.ActualLinearResponseBesselSlack.original_bessel_remaining_nonneg
#print axioms KLSConstantImprovement.ActualLinearResponseBesselSlack.exact_actual_linear_slack
#print axioms KLSConstantImprovement.ActualLinearResponseBesselSlack.actual_linear_response_cap_with_deficits
#print axioms KLSConstantImprovement.ActualLinearResponseBesselSlack.actual_seven_halves_response_completion

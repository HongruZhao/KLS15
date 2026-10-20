import KLSConstantImprovement.ActualCubicQuadraticDeficit
import KLSConstantImprovement.QuadraticCovarianceCharge
import ActualCubicCreationBound

/-! Original third projection/exchange bounds and the critical heat payment.
The first two declarations are actual-law statements on literal polynomials.
The last two are scalar conversions of the explicitly supplied heat identity
and directional Schur estimate. Actual tilt/damping derivative identification
remains the paper bridge; no unconditional derivative identity is assumed
silently. Fresh draft only; no builds or accepted-source edits by the author. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix InnerProductSpace
open scoped BigOperators
namespace KLSConstantImprovement.OriginalUpperRecovery6CriticalCurvature
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise KLSBelow25.CubicCreation
open ActualCubicGradientEnergy ActualCubicQuadraticDeficit QuadraticCovarianceCharge
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def originalThirdProjectionSq {n : ℕ} (μ : Measure (Space n))
    (G : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖covarianceVector μ (ActualCubicGradientEnergy.centeredQuadratic G)‖^2

def originalThirdExchange {n : ℕ} (μ : Measure (Space n))
    (G : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  cross (lawCubicSlotArray μ G)

theorem originalThirdProjectionSq_le_eight {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.IsSymm) :
    originalThirdProjectionSq μ G ≤ 8*matrixFrobeniusSq G := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  exact (covarianceVector_norm_sq_le_variance hμ.isotropic
    (ActualCubicPoincareFourthSector.centeredQuadratic_memLp hμ G)).trans
      (centeredQuadratic_variance_le_eight hμ G hG)

theorem originalThirdExchange_le_four {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.IsSymm) :
    originalThirdExchange μ G ≤ 4*matrixFrobeniusSq G := by
  have hsym : ∀ i j,G i j=G j i := by
    intro i j
    exact congrFun (congrFun hG j) i
  have hb := lawCubicSlotArray_cross_le_four hμ G hsym
  simpa only [originalThirdExchange,matrixSquare,matrixFrobeniusSq] using hb

theorem critical_curvature_from_original_heat_identity
    {n : ℕ} {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.IsSymm)
    {damping traceCurvature : ℝ} (hdamping : 0 ≤ damping)
    (hheat : damping+traceCurvature/2 =
      12*matrixFrobeniusSq G+originalThirdProjectionSq μ G+8*originalThirdExchange μ G) :
    traceCurvature ≤ 104*matrixFrobeniusSq G := by
  have hp := originalThirdProjectionSq_le_eight hμ G hG
  have hx := originalThirdExchange_le_four hμ G hG
  linarith

theorem critical_contracted_payment {R d traceCurvature e : ℝ}
    (hd : 0 ≤ d) (htrace : traceCurvature ≤ 104*R)
    (hschur : e^2 ≤ d*traceCurvature/2) : e^2 ≤ 52*R*d := by
  have hp := mul_le_mul_of_nonneg_left htrace hd
  nlinarith

end KLSConstantImprovement.OriginalUpperRecovery6CriticalCurvature
#print axioms KLSConstantImprovement.OriginalUpperRecovery6CriticalCurvature.originalThirdProjectionSq_le_eight
#print axioms KLSConstantImprovement.OriginalUpperRecovery6CriticalCurvature.originalThirdExchange_le_four
#print axioms KLSConstantImprovement.OriginalUpperRecovery6CriticalCurvature.critical_curvature_from_original_heat_identity
#print axioms KLSConstantImprovement.OriginalUpperRecovery6CriticalCurvature.critical_contracted_payment

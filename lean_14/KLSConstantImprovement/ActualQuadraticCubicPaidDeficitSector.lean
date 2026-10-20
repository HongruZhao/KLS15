import KLSConstantImprovement.ActualObservationFourthDeficit
import KLSConstantImprovement.ActualAffineSameTestCreationCubicSeed238452Cap

/-! A genuine all-law large-deficit sector of a proposed paid cross36 bound.
The sector follows from the accepted raw cap on the original centered
quadratic. It does not claim the remaining small-deficit theorem.
No compilation or accepted-source edits by the author. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace KLSConstantImprovement.OriginalUpperRecovery6QuadraticPaidSector
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open ActualCubicGradientEnergy ActualCubicAffineRegression ActualCubicPoincareFourthSector
open ActualCubicQuadraticDeficit
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def quadraticFourthDeficit {n : ℕ} (μ : Measure (Space n))
    (G : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  8*matrixFrobeniusSq G-ProbabilityTheory.variance (ActualCubicGradientEnergy.centeredQuadratic G) μ

theorem original_quadratic_cubic_deficit_cap {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (G : Matrix (Fin n) (Fin n) ℝ) :
    actualAppellEnergy μ (ActualCubicGradientEnergy.centeredQuadratic G) 3 ≤
      (536517/625 : ℝ)*(8*matrixFrobeniusSq G-quadraticFourthDeficit μ G) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hcap := actual_appell_energy_three_affine_same_test_creation238452_le_integral
    hμ (centeredQuadratic_memLp hμ G)
  have hH : (36*AffineSameTestCreationSeed238452.B : ℝ)=536517/625 := by
    norm_num [AffineSameTestCreationSeed238452.B]
  have hi : (∫ x,(ActualCubicGradientEnergy.centeredQuadratic G x)^2 ∂μ)=
      ProbabilityTheory.variance (ActualCubicGradientEnergy.centeredQuadratic G) μ := by
    rw [integral_centeredQuadratic_sq hμ G,centeredQuadratic_variance_eq hμ G]
  rw [hH,hi] at hcap
  unfold quadraticFourthDeficit
  convert hcap using 1 <;> ring

theorem original_quadratic_cubic_paid_large_deficit {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (G : Matrix (Fin n) (Fin n) ℝ)
    (hsector : (3482136/1346517 : ℝ)*matrixFrobeniusSq G ≤ quadraticFourthDeficit μ G) :
    actualAppellEnergy μ (ActualCubicGradientEnergy.centeredQuadratic G) 3 ≤
      1296*(matrixFrobeniusSq G+quadraticFourthDeficit μ G) := by
  have hcap := original_quadratic_cubic_deficit_cap hμ G
  linarith

end KLSConstantImprovement.OriginalUpperRecovery6QuadraticPaidSector
#print axioms KLSConstantImprovement.OriginalUpperRecovery6QuadraticPaidSector.original_quadratic_cubic_deficit_cap
#print axioms KLSConstantImprovement.OriginalUpperRecovery6QuadraticPaidSector.original_quadratic_cubic_paid_large_deficit

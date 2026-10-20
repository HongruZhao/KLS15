import TripleTensorCoordinates
import ActualFourthCumulantCoordinates
import ActualCreationCubicSeed24Cap

noncomputable section
open MeasureTheory InnerProductSpace
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext
open KLSBelow25.PairTensor KLSBelow25.TripleTensor KLSBelow25.TripleProjection
variable {n r : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem actual_fourth_cumulant_one_three_square_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (v : Fin n→ℝ) :
    (∑ α : Fin 3→Fin n,(∑ m,actualFourthCumulantArray μ (α 0) (α 1) (α 2) m*v m)^2) ≤
      864*(∑ m,(v m)^2) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  let u : Space n := WithLp.toLp 2 v
  have he (α : Fin 3→Fin n) :
      (∑ m,actualFourthCumulantArray μ (α 0) (α 1) (α 2) m*v m)=
        actualAppellCoefficient μ (fun x => inner ℝ x u) 3 α := by
    rw [actualAppellCoefficient_inner_eq_cumulant hμ.logConcave,
      cumulantTensor_snoc_coordinate_sum]
    simp only [EuclideanSpace.basisFun_apply]
    simp_rw [actual_cumulant_four_snoc_coordinate hμ]
    apply Finset.sum_congr rfl
    intro m _
    change _=v m*_
    ring
  simp_rw [he]
  have hb := actual_appell_energy_three_creation24_le_integral hμ (hμ.isotropic.memLp_inner u)
  rw [hμ.isotropic.integral_inner_sq,EuclideanSpace.real_norm_sq_eq] at hb
  norm_num only [KLSBelow25.CreationSeed24.B] at hb
  simpa only [actualAppellEnergy,u] using hb

theorem actual_triple_kernel_square_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (H : Tensor (ι:=Fin n) (r+1)) (e : Triple (r+3)) :
    square (KLSBelow25.TripleTensor.kernel (actualFourthCumulantArray μ) H e) ≤864*square H :=
  kernel_square_le _ H e (actual_fourth_cumulant_one_three_square_le hμ)

theorem actual_triple_kernel_cross_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (H : Tensor (ι:=Fin n) (r+1)) (e f : Triple (r+3)) :
    pairing (KLSBelow25.TripleTensor.kernel (actualFourthCumulantArray μ) H e)
      (KLSBelow25.TripleTensor.kernel (actualFourthCumulantArray μ) H f) ≤864*square H :=
  kernel_pairing_le _ H e f (actual_fourth_cumulant_one_three_square_le hμ)

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actual_fourth_cumulant_one_three_square_le
#print axioms KLS.DeterministicBridgeIntegration.actual_triple_kernel_square_le

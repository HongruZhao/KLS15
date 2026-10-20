import ActualTiltLowOrder
import ActualJointL2QuotientMaximizer
import KLS.QuadraticCovarianceOperator
import KLS.FullQuadraticVarianceBound

/-! Literal full-class degree-two Appell seed. The old unconditional
quadratic-variance-eight theorem is reused with exact ordered-index and
factorial normalization; no coefficient estimate is assumed. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix ProbabilityTheory
open scoped ContDiff BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem actualAppellCoefficient_two_eq_quadraticCovariance
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (a : Fin 2 → Fin n) :
    actualAppellCoefficient μ f 2 a=quadraticCovarianceMatrix μ f (a 0) (a 1) := by
  have hs := contDiffAt_normalized_tilt_average hμ.logConcave hf
  have hd := ((hs.of_le (by simp) : ContDiffAt ℝ 2 _ _).fderiv_right
    (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [actualAppellCoefficient,iteratedFDeriv_two_apply,
    ←coordinateHessian_eq_fderiv_fderiv hd,
    coordinateHessian_normalized_tilt_zero_of_isotropic hμ.logConcave hμ.isotropic hf]
  rw [quadraticCovarianceMatrix,covariance_eq_sub hf
    (hμ.quadraticVarianceEight_unconditional.memLp_coordinate_mul (a 0) (a 1)),
    hμ.isotropic.integral_coordinate_mul]
  rfl

def pairTupleEquiv (n : ℕ) : (Fin 2 → Fin n) ≃ Fin n × Fin n where
  toFun a := (a 0,a 1)
  invFun p := ![p.1,p.2]
  left_inv a := by funext i; fin_cases i <;> simp
  right_inv p := by simp

theorem actualAppellEnergy_two_eq_frobenius
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    actualAppellEnergy μ f 2=matrixFrobeniusSq (quadraticCovarianceMatrix μ f) := by
  unfold actualAppellEnergy
  simp_rw [actualAppellCoefficient_two_eq_quadraticCovariance hμ hf]
  change (∑ a : Fin 2 → Fin n, (quadraticCovarianceMatrix μ f (a 0) (a 1))^2)=
    ∑ i, ∑ j, (quadraticCovarianceMatrix μ f i j)^2
  calc
    _ = ∑ p : Fin n × Fin n, (quadraticCovarianceMatrix μ f p.1 p.2)^2 :=
      Fintype.sum_equiv (pairTupleEquiv n) _ _ (fun _ => rfl)
    _ = _ := Fintype.sum_prod_type _

theorem actualAppellEnergy_two_le_eight_norm_sq
    (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) :
    actualAppellEnergy μ f 2 ≤ 8*‖f‖^2 := by
  rw [actualAppellEnergy_two_eq_frobenius hμ (Lp.memLp f)]
  exact hμ.quadraticVarianceEight_unconditional.quadraticCovariance_frobeniusSq_le_norm f

theorem actualAppellEnergy_two_le_eight_integral
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    actualAppellEnergy μ f 2 ≤ 8*(∫ x, (f x)^2 ∂μ) := by
  rw [actualAppellEnergy_two_eq_frobenius hμ hf]
  have hb := hμ.quadraticVarianceEight_unconditional.quadraticCovariance_frobeniusSq_le_norm
    (hf.toLp f)
  rw [quadraticCovarianceMatrix_congr_ae hf.coeFn_toLp,actualLp_norm_sq_eq_integral] at hb
  have he : (fun x => ((hf.toLp f) x)^2) =ᵐ[μ] fun x => (f x)^2 := by
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
  rw [integral_congr_ae he] at hb
  exact hb

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actualAppellEnergy_two_le_eight_norm_sq
#print axioms KLS.DeterministicBridgeNext.actualAppellEnergy_two_le_eight_integral

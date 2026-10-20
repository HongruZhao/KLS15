import KLSConstantImprovement.ActualFixedTensorDeficit
import ActualAppellMultiplication

/-! Exact first, second, and third coordinate moment formulas for the
actual tilted law on its local exponential domain. -/
noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped ContDiff Topology
namespace KLSConstantImprovement.ActualTiltCubicMoment
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open ActualFixedTensorDeficit
variable {n : ℕ}
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem actualTiltMean_eq_jet {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {r : ℝ} (h1 : LocalNormExponentialDomain μ (fun _=>1) r)
    {θ : Space n} (hθ : ‖θ‖<r) (i : Fin n) :
    actualTiltMeanCoordinate μ i θ=cumulantJet μ [i] θ := by
  unfold actualTiltMeanCoordinate
  rw [actualDampedAverage_zero_eq_tilt_average]
  have he:=fderiv_logLaplace_direction_eq_average_of_local h1 hθ (e i)
  simpa [cumulantJet,directionalWordDerivative,e,EuclideanSpace.inner_single_right] using he.symm

theorem actualTiltMean_derivative_eq_jet {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {r : ℝ} (h1 : LocalNormExponentialDomain μ (fun _=>1) r)
    {θ : Space n} (hθ : ‖θ‖<r) (i j : Fin n) :
    coordinateDerivative (actualTiltMeanCoordinate μ j) i θ=cumulantJet μ [i,j] θ := by
  have he:actualTiltMeanCoordinate μ j =ᶠ[𝓝 θ] cumulantJet μ [j] := by
    filter_upwards [isOpen_ball.mem_nhds (show θ∈ball 0 r by simpa using hθ)] with z hz
    exact actualTiltMean_eq_jet h1 (by simpa using hz) j
  unfold coordinateDerivative
  rw [he.fderiv_eq]
  rfl

theorem actualTiltPair_eq_jet {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {r : ℝ} (h1 : LocalNormExponentialDomain μ (fun _=>1) r)
    {θ : Space n} (hθ : ‖θ‖<r) (j k : Fin n) :
    actualDampedAverage μ (fun x=>x j*x k) 0 θ=
      cumulantJet μ [j,k] θ+cumulantJet μ [j] θ*cumulantJet μ [k] θ := by
  have hk:LocalNormExponentialDomain μ (fun x : Space n=>x k) r := by
    simpa only [one_mul] using h1.mul_coordinate k
  rw [actualDampedAverage_coordinate_mul_of_local hk h1 hθ j]
  change coordinateDerivative (actualTiltMeanCoordinate μ k) j θ+
    actualTiltMeanCoordinate μ j θ*actualTiltMeanCoordinate μ k θ=_
  rw [actualTiltMean_derivative_eq_jet h1 hθ,actualTiltMean_eq_jet h1 hθ,
    actualTiltMean_eq_jet h1 hθ]

theorem actualTiltCubic_eq_jet {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {r : ℝ} (h1 : LocalNormExponentialDomain μ (fun _=>1) r)
    {θ : Space n} (hθ : ‖θ‖<r) (i j k : Fin n) :
    actualDampedAverage μ (fun x=>x i*(x j*x k)) 0 θ=
      cumulantJet μ [i,j,k] θ+
      cumulantJet μ [i,j] θ*cumulantJet μ [k] θ+
      cumulantJet μ [i,k] θ*cumulantJet μ [j] θ+
      cumulantJet μ [j,k] θ*cumulantJet μ [i] θ+
      cumulantJet μ [i] θ*cumulantJet μ [j] θ*cumulantJet μ [k] θ := by
  have hk:LocalNormExponentialDomain μ (fun x : Space n=>x k) r := by
    simpa only [one_mul] using h1.mul_coordinate k
  have hjk:LocalNormExponentialDomain μ (fun x : Space n=>x j*x k) r := by
    simpa only [mul_comm] using hk.mul_coordinate j
  have hz:θ∈ball 0 r := by simpa using hθ
  have hs (is : List (Fin n)) : DifferentiableAt ℝ (cumulantJet μ is) θ :=
    ((cumulantJet_contDiffOn h1 is).contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt (by simp)
  have he:actualDampedAverage μ (fun x=>x j*x k) 0 =ᶠ[𝓝 θ]
      (fun z=>cumulantJet μ [j,k] z+cumulantJet μ [j] z*cumulantJet μ [k] z) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with z hz'
    exact actualTiltPair_eq_jet h1 (by simpa using hz') j k
  have hd:coordinateDerivative (actualDampedAverage μ (fun x=>x j*x k) 0) i θ=
      cumulantJet μ [i,j,k] θ+
      cumulantJet μ [i,j] θ*cumulantJet μ [k] θ+
      cumulantJet μ [j] θ*cumulantJet μ [i,k] θ := by
    unfold coordinateDerivative
    rw [he.fderiv_eq]
    change coordinateDerivative (fun z=>cumulantJet μ [j,k] z+
      cumulantJet μ [j] z*cumulantJet μ [k] z) i θ=_
    change coordinateDerivative ((cumulantJet μ [j,k])+
      (fun z=>cumulantJet μ [j] z*cumulantJet μ [k] z)) i θ=_
    rw [coordinateDerivative_add (f:=cumulantJet μ [j,k])
        (g:=fun z=>cumulantJet μ [j] z*cumulantJet μ [k] z)
        (hs [j,k]) ((hs [j]).mul (hs [k])),
      coordinateDerivative_mul (f:=cumulantJet μ [j]) (g:=cumulantJet μ [k])
        (hs [j]) (hs [k]),derivative_cumulantJet,
      derivative_cumulantJet,derivative_cumulantJet]
    ring
  rw [actualDampedAverage_coordinate_mul_of_local hjk h1 hθ i,hd,
    actualTiltMean_eq_jet h1 hθ,actualTiltPair_eq_jet h1 hθ]
  ring

end KLSConstantImprovement.ActualTiltCubicMoment
#print axioms KLSConstantImprovement.ActualTiltCubicMoment.actualTiltMean_eq_jet
#print axioms KLSConstantImprovement.ActualTiltCubicMoment.actualTiltMean_derivative_eq_jet
#print axioms KLSConstantImprovement.ActualTiltCubicMoment.actualTiltPair_eq_jet
#print axioms KLSConstantImprovement.ActualTiltCubicMoment.actualTiltCubic_eq_jet

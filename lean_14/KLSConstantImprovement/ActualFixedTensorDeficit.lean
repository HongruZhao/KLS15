import ActualAppellCumulantDrift
import ActualProperCubicCreation
import ActualFourthCumulantCoordinates
import KLSConstantImprovement.ActualDeficitTensorBounds

/-! Actual fixed-tensor quadratic deficit along the original-law tilt.
The covariance and cumulants are local derivatives of the genuine log
Laplace transform. No compact-support or global smoothness premise is used.
-/
noncomputable section
open MeasureTheory Matrix Set Filter Metric
open scoped BigOperators ContDiff Topology
namespace KLSConstantImprovement.ActualFixedTensorDeficit
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
variable {n : ℕ}
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

def e (i : Fin n) : Space n := EuclideanSpace.single i 1
def cumulantJet (μ : Measure (Space n)) (is : List (Fin n)) (θ : Space n) : ℝ :=
  directionalWordDerivative (tiltLogLaplace μ) (is.map e) θ
def covarianceJet (μ : Measure (Space n)) (a b : Fin n) : Space n → ℝ :=
  cumulantJet μ [a,b]
def fixedTensorDeficit (μ : Measure (Space n)) (B C : Matrix (Fin n) (Fin n) ℝ)
    (θ : Space n) : ℝ :=
  ∑ a,∑ b,∑ c,∑ d,B a b*C c d*
    (6*covarianceJet μ a c θ*covarianceJet μ b d θ-cumulantJet μ [a,b,c,d] θ)
def contractedDeficitHessian (μ : Measure (Space n))
    (T : KLSBelow25.CubicSymmetricNoise.Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,coordinateHessian (fixedTensorDeficit μ (T i) (T j)) 0 i j
def sixthContraction (μ : Measure (Space n))
    (T : KLSBelow25.CubicSymmetricNoise.Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ a,∑ b,∑ c,∑ d,T i a b*T j c d*cumulantJet μ [i,j,a,b,c,d] 0

theorem cumulantJet_zero {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) (is : List (Fin n)) :
    cumulantJet μ is 0=listCumulant μ (is.map e) :=
  (listCumulant_eq_local_word hLC _).symm

theorem cumulantJet_contDiffOn {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    {r : ℝ} (h1 : LocalNormExponentialDomain μ (fun _=>1) r) (is : List (Fin n)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (cumulantJet μ is) (ball 0 r) :=
  contDiffOn_word_of_isOpen isOpen_ball (contDiffOn_logLaplace_of_local h1) _

theorem derivative_cumulantJet (μ : Measure (Space n)) (is : List (Fin n)) (i : Fin n) :
    coordinateDerivative (cumulantJet μ is) i=cumulantJet μ (i::is) := rfl
theorem hessian_cumulantJet (μ : Measure (Space n)) (is : List (Fin n))
    (θ : Space n) (i j : Fin n) :
    coordinateHessian (cumulantJet μ is) θ i j=cumulantJet μ (i::j::is) θ := rfl

theorem covarianceJet_zero {μ : Measure (Space n)} (hμ : admissibleMeasure μ) (a b : Fin n) :
    covarianceJet μ a b 0=if a=b then 1 else 0 := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  rw [covarianceJet,cumulantJet_zero hμ.logConcave]
  have hh:=actualTiltMean_word_eq_cumulant hμ.logConcave b [e a]
  have hs:=actualTiltMean_singleton_of_isotropic hμ.logConcave hμ.isotropic b (e a)
  simp only [List.map_cons,List.map_nil,List.cons_append,List.nil_append] at *
  change directionalWordDerivative (actualTiltMeanCoordinate μ b) [e a] 0 =
    listCumulant μ [e a,e b] at hh
  rw [←hh,hs]
  simp [e,eq_comm]

theorem cumulantJet_three_zero {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (i a b : Fin n) : cumulantJet μ [i,a,b] 0=actualThirdCubicArray μ i a b := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  rw [cumulantJet_zero hμ.logConcave]
  exact actual_list_cumulant_three_coordinate hμ i a b

theorem cumulantJet_four_zero {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (i j a b : Fin n) : cumulantJet μ [i,j,a,b] 0=actualFourthCumulantArray μ i j a b := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨r,hr,h1⟩:=hμ.logConcave.exists_localNormExponentialDomain_one
  have hh:=local_word_ofFn isOpen_ball (contDiffOn_logLaplace_of_local h1)
    ![e i,e j,e a,e b] (show (0 : Space n)∈ball 0 r by simpa using hr)
  simpa [cumulantJet,e,actualFourthCumulantArray,cumulantTensor,List.ofFn_succ] using hh

theorem covariance_product_hessian {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (a b c d i j : Fin n) :
    coordinateHessian (fun θ=>covarianceJet μ a c θ*covarianceJet μ b d θ) 0 i j =
      actualFourthCumulantArray μ i j a c*(if b=d then 1 else 0)+
      actualThirdCubicArray μ j a c*actualThirdCubicArray μ i b d+
      actualThirdCubicArray μ i a c*actualThirdCubicArray μ j b d+
      (if a=c then 1 else 0)*actualFourthCumulantArray μ i j b d := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨r,hr,h1⟩:=hμ.logConcave.exists_localNormExponentialDomain_one
  have hz:(0 : Space n)∈ball 0 r := by simpa using hr
  have hc (a b : Fin n) : ContDiffAt ℝ 2 (covarianceJet μ a b) 0 :=
    ((cumulantJet_contDiffOn h1 [a,b]).contDiffAt (isOpen_ball.mem_nhds hz)).of_le (by simp)
  rw [coordinateHessian_mul_of_contDiffAt (hc a c) (hc b d)]
  simp only [covarianceJet,derivative_cumulantJet,hessian_cumulantJet,
    cumulantJet_three_zero hμ,cumulantJet_four_zero hμ]
  change _ = _
  rw [←covarianceJet,covarianceJet_zero hμ,←covarianceJet,covarianceJet_zero hμ]
  ring

end KLSConstantImprovement.ActualFixedTensorDeficit
#print axioms KLSConstantImprovement.ActualFixedTensorDeficit.cumulantJet_zero
#print axioms KLSConstantImprovement.ActualFixedTensorDeficit.covarianceJet_zero
#print axioms KLSConstantImprovement.ActualFixedTensorDeficit.cumulantJet_three_zero
#print axioms KLSConstantImprovement.ActualFixedTensorDeficit.cumulantJet_four_zero
#print axioms KLSConstantImprovement.ActualFixedTensorDeficit.covariance_product_hessian

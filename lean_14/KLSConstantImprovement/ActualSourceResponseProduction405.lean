import KLSConstantImprovement.ActualResponseProductionAlgebra405
import KLSConstantImprovement.ActualBilinearConnectionContractions405
import KLSConstantImprovement.ActualQuadraticResponseMetricFlux405
import KLSConstantImprovement.ActualQuadraticResponseRowEquation405
import KLSConstantImprovement.ActualSourceConnectionPointwise405
import KLSConstantImprovement.ActualSourceQuarticBinding405

/-! Literal positive production of the constructed response rows. The
actual raw first-derivative contractions complete to B_F, which is PSD.
This file supplies the pointwise binding, not an assumed weak production
PDE; the compact integral identity is a separate actual-test assembly. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualSourceResponseProduction405
open KLS ActualBoundedCanonicalSource ActualQuadraticResponseField405 ActualQuadraticResponseGramLocal405
open ActualQuadraticResponseMetricFlux405 ActualQuadraticResponseRowEquation405
open ActualResponseProductionAlgebra405 ActualBilinearConnectionContractions405
open ActualSourceHessianEvolution405 ActualSourceConnectionFields405 ActualSourceConnectionPointwise405
open ActualSourceCurvatureDomains405 ActualSourceQuarticBinding405 ActualSourceTensorGramMetricBinding
open ActualCanonicalConnectionAlgebra405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

def actualResponseProduction (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  responseProductionMatrix (coordinateHessian d.potential x) (coordinateHessian d.potential x)⁻¹
    (sourceTargetCurvature d x) (quadraticResponseMatrix d T x)
    (fun i => sourceThirdAlong d (fun a y => quadraticResponseMatrix d T y i a) x)
    (fun i => responseRowJacobian d hn hμ T i x) T

def responseRawForcing (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) (x : Space n) : ℝ :=
  ∑ a, (actualTraceRawDerivative d T i a x * quadraticResponseMatrix d T x j a +
    quadraticResponseMatrix d T x i a * actualTraceRawDerivative d T j a x)

def responseRawSourcePair (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) (x : Space n) : ℝ :=
  ∑ a, ∑ b, sourceConnectionCurvature d x a b * quadraticResponseMatrix d T x i a *
    quadraticResponseMatrix d T x j b

def responseRawJacobianPair (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (x : Space n) : ℝ :=
  ∑ a, ∑ b, quadraticResponseDerivative d hn hμ T i a b x * quadraticResponseDerivative d hn hμ T j b a x

def responseRawConnectionPair (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (x : Space n) : ℝ :=
  ∑ a, ∑ b, ∑ r, ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x a) r b *
    (quadraticResponseDerivative d hn hμ T i a r x * quadraticResponseMatrix d T x j b +
      quadraticResponseMatrix d T x i a * quadraticResponseDerivative d hn hμ T j b r x)

def actualResponseRawRHS (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (x : Space n) : ℝ :=
  responseRawForcing d T i j x - quadraticResponseGram d T x i j - responseRawSourcePair d T i j x -
    2 * responseRawJacobianPair d hn hμ T i j x - responseRawConnectionPair d hn hμ T i j x

theorem actualResponseProduction_posSemidef_ae (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j) :
    ∀ᵐ x ∂potentialMeasure d.potential, (actualResponseProduction d hn hμ T x).PosSemidef := by
  filter_upwards [d.hessian_ae_source,
    ae_all_iff.mpr (fun i => sourceThirdAlong_isSymm_ae d (fun a y => quadraticResponseMatrix d T y i a)),
    ae_all_iff.mpr (actual_quadratic_response_compatible_ae d hn hμ T h12 h23)] with x hx hN hD
  have hV := coordinateHessian_posSemidef_of_convex
    (d.target_smooth.of_le (by simp)) d.target_convex_potential (gradient d.potential x)
  have hP : (sourceTargetCurvature d x).PosSemidef := by
    simpa only [sourceTargetCurvature, hx.1.isHermitian.eq] using
      hV.conjTranspose_mul_mul_same (coordinateHessian d.potential x)
  exact responseProductionMatrix_posSemidef _ _ _ hx.1 hP _ _ _ hN
    (fun i => Matrix.IsSymm.ext fun a b => h23 i b a) hD

private theorem row_source_pair (P F : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (∑ a, ∑ b, P a b * F i a * F j b) = (F * P * F.transpose) i j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

theorem actual_response_raw_production_binding_ae (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    actualResponseRawRHS d hn hμ T i j =ᵐ[potentialMeasure d.potential] fun x =>
      2 * sourceTensorGramEntry d.potential T i j x - quadraticResponseGram d T x i j -
        actualResponseProduction d hn hμ T x i j := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source, d.third_symmetric_ae.filter_mono hac.ae_le] with x hx hN
  let H := coordinateHessian d.potential x
  let J := H⁻¹
  let F := quadraticResponseMatrix d T x
  let Di := responseRowJacobian d hn hμ T i x
  let Dj := responseRowJacobian d hn hμ T j x
  let Nu := sourceThirdAlong d (fun a y => quadraticResponseMatrix d T y i a) x
  let Nv := sourceThirdAlong d (fun a y => quadraticResponseMatrix d T y j a) x
  let P := sourceTargetCurvature d x
  have hHJ : H * J = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hx.1.isUnit)
  have htrace (k a : Fin n) : actualTraceRawDerivative d T k a x = (T k * sourceThirdMatrix d x a).trace := by
    rfl
  have hforce : responseRawForcing d T i j x = (T i * Nv).trace + (T j * Nu).trace := by
    simp only [responseRawForcing, htrace, Finset.sum_add_distrib]
    rw [trace_tensor_forcing (T i) (sourceThirdMatrix d x) (F j)]
    congr 1
    calc
      _ = ∑ a, (T j * sourceThirdMatrix d x a).trace * F i a :=
        Finset.sum_congr rfl fun a _ => mul_comm _ _
      _ = _ := trace_tensor_forcing _ _ _
  have hsource : responseRawSourcePair d T i j x =
      (F * P * F.transpose) i j + (J * Nu * J * Nv).trace := by
    change (∑ a, ∑ b, (P a b + matrixTraceGram J (sourceThirdMatrix d x) a b) * F i a * F j b) = _
    simp only [add_mul, Finset.sum_add_distrib]
    rw [row_source_pair P F i j, traceGram_bilinear J (sourceThirdMatrix d x) (F i) (F j)]
    rfl
  have hjac : responseRawJacobianPair d hn hμ T i j x = (Di * Dj).trace := by
    simp only [responseRawJacobianPair, Di, Dj, responseRowJacobian, Matrix.trace, Matrix.diag_apply,
      Matrix.mul_apply, Matrix.of_apply]
  have hconn : responseRawConnectionPair d hn hμ T i j x =
      (Di * J * Nv).trace + (Dj * J * Nu).trace :=
    connection_cross_bilinear J Di Dj (sourceThirdMatrix d x) hN (F i) (F j)
  have he := response_production_completion H J Nu Nv Di Dj (T i) (T j) hHJ
  rw [actualResponseRawRHS, hforce, hsource, hjac, hconn,
    sourceTensorGramEntry_eq_trace]
  change _ = 2 * (T i * H * T j * H).trace - quadraticResponseGram d T x i j -
    ((F * P * F.transpose) i j +
      (completionLeft H J Nu Di (T i) * completionLeft H J Nv Dj (T j)).trace +
      (completionRight H Di (T i) * completionRight H Dj (T j)).trace)
  linarith

end KLSConstantImprovement.ActualSourceResponseProduction405

#print axioms KLSConstantImprovement.ActualSourceResponseProduction405.actualResponseProduction_posSemidef_ae
#print axioms KLSConstantImprovement.ActualSourceResponseProduction405.actual_response_raw_production_binding_ae

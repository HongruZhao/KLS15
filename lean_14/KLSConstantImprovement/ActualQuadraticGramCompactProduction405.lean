import KLSConstantImprovement.ActualQuadraticGramProduction405
import KLSConstantImprovement.ActualQuadraticFluxProductTests405
import KLSConstantImprovement.ActualResponseLocalEquations405
import KLSConstantImprovement.ActualGramProductionAssemblyAlgebra405
import KLSConstantImprovement.ActualBilinearConnectionContractions405
import KLSConstantImprovement.ActualCompatibleGramFlux405
import KLSConstantImprovement.ActualLocalDivergenceMetricEquation405

/-! Genuine compact whole-row production for the same natural quadratic
inverses. The actual differentiated quadratic row equations and the
actual H equation construct the production equation; no PDE witness is
supplied as an input. -/
noncomputable section
open MeasureTheory Matrix Set Filter
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualQuadraticGramCompactProduction405
open KLS ActualBoundedCanonicalSource ActualQuadraticGramProduction405 ActualQuadraticJacobianEnergy405
open ActualQuadraticResponseField405 ActualQuadraticHilbertMatrix405 ActualQuadraticRowCurvature405
open ActualQuadraticFluxProductTests405 ActualQuadraticRowWeakTests405 ActualQuadraticRowEquation405
open ActualSourceLocalDivergence405 ActualResponseLocalEquations405 ActualGramProductionAssemblyAlgebra405
open ActualLocalBoundedWeakAlgebra405 ActualSourceConnectionFields405 ActualSourceHessianEvolution405
open ActualSourceCurvatureDomains405 ActualBilinearConnectionContractions405 ActualCompatibleGramFlux405
open ActualLocalDivergenceMetricEquation405 ActualBoundedWeakGlobalForm405
open ActualSourceQuadraticEta405 ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
open ActualSourceNaturalHessian405 ActualBoundedRawTestAlgebra405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
variable {n : ℕ} {μ : Measure (Space n)}

private theorem flux_fin3 {d : SourceData μ} (e : Fin 3 → SourceLocalDivergence d)
    (a : Fin n) (x : Space n) :
    (sourceLocalDivergenceSum e).flux a x = (e 0).flux a x + (e 1).flux a x + (e 2).flux a x := by
  simp [sourceLocalDivergenceSum, Fin.sum_univ_succ, add_assoc]

private theorem drift_fin3 {d : SourceData μ} (e : Fin 3 → SourceLocalDivergence d) (x : Space n) :
    (sourceLocalDivergenceSum e).drift x = (e 0).drift x + (e 1).drift x + (e 2).drift x := by
  simp [sourceLocalDivergenceSum, Fin.sum_univ_succ, add_assoc]

private theorem row_source_pair (P F : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (∑ a, ∑ b, P a b * F i a * F j b) = (F * P * F.transpose) i j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

theorem whole_row_completion (J Nu Nv Du Dv : Matrix (Fin n) (Fin n) ℝ) :
    (J * Nu * J * Nv).trace + 2 * (Du * Dv).trace +
      ((Du * J * Nv).trace + (Dv * J * Nu).trace) =
        ((Du + J * Nu) * (Dv + J * Nv)).trace + (Du * Dv).trace := by
  have hc : (J * Nu * Dv).trace = (Dv * J * Nu).trace := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (J * Nu) Dv
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.trace_add, ← Matrix.mul_assoc, hc]
  ring

section Fixed
variable (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C)

def quadraticGramLocalTest (i j : Fin n) : LocalRawTest n :=
  localRawTestSum fun b : Fin n => localRawTestSum fun a : Fin n =>
    ((quadraticFluxLocalTest d hn hμ (T i) hC (hM i) a).mul
      (LocalRawTest.ofBoundedRawTest (BoundedRawTest.hessian d a b))).mul
        (quadraticFluxLocalTest d hn hμ (T j) hC (hM j) b)

def quadraticGramRawDerivative (i j r : Fin n) (x : Space n) : ℝ :=
  ∑ b, ∑ a, ((quadraticFluxJacobian d hn hμ (T i) a r x * coordinateHessian d.potential x a b +
    quadraticRowFlux d T i a x * d.third x r a b) * quadraticRowFlux d T j b x +
      (quadraticRowFlux d T i a x * coordinateHessian d.potential x a b) * quadraticFluxJacobian d hn hμ (T j) b r x)

theorem quadraticGramLocalTest_value (i j : Fin n) (x : Space n) :
    (quadraticGramLocalTest d hn hμ T hC hM i j).value x = actualQuadraticGram d T x i j := by
  change (∑ b, ∑ a, (quadraticRowFlux d T i a x * coordinateHessian d.potential x a b) *
    quadraticRowFlux d T j b x) = _
  simp only [actualQuadraticGram, actualQuadraticFluxMatrix, Matrix.of_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]

theorem quadraticGramLocalTest_derivative (i j r : Fin n) (x : Space n) :
    (quadraticGramLocalTest d hn hμ T hC hM i j).derivative r x = quadraticGramRawDerivative d hn hμ T i j r x := rfl

def quadraticFluxRowEquation (i a : Fin n) : SourceLocalDivergence d where
  flux := fun r => quadraticFluxJacobian d hn hμ (T i) r a
  drift := quadraticRowDrift d (T i) a
  flux_local := fun r E hE => quadratic_flux_jacobian_local_L2 d hn hμ (T i) r a hE
  drift_local := locallyIntegrable_of_memLp_two_on_compacts (quadraticRowDrift_local_L2 d hn hμ (T i) a)
  identity := fun _ hψ hc => actual_quadratic_row_drift_compact_test d hn hμ (T i) a hψ hc

def quadraticRowTimesEquation (i j : Fin n) : SourceLocalDivergence d :=
  sourceLocalDivergenceSum fun a : Fin n => (quadraticFluxRowEquation d hn hμ T i a).mulLocal
    (quadraticFluxLocalTest d hn hμ (T j) hC (hM j) a)

def quadraticHessianTimesEquation (i j : Fin n) : SourceLocalDivergence d :=
  sourceLocalDivergenceSum fun a : Fin n => sourceLocalDivergenceSum fun b : Fin n =>
    (sourceHessianEntryEquation d a b).mulLocal
      ((quadraticFluxLocalTest d hn hμ (T i) hC (hM i) a).mul
        (quadraticFluxLocalTest d hn hμ (T j) hC (hM j) b))

def quadraticAssembledEquation (i j : Fin n) : SourceLocalDivergence d :=
  sourceLocalDivergenceSum fun k : Fin 3 =>
    ![quadraticRowTimesEquation d hn hμ T hC hM i j,
      quadraticRowTimesEquation d hn hμ T hC hM j i,
      quadraticHessianTimesEquation d hn hμ T hC hM i j] k

theorem quadraticAssembledEquation_flux_spec (i j r : Fin n) (x : Space n) :
    (quadraticAssembledEquation d hn hμ T hC hM i j).flux r x =
      (∑ a, quadraticRowFlux d T j a x * quadraticFluxJacobian d hn hμ (T i) r a x) +
      (∑ a, quadraticRowFlux d T i a x * quadraticFluxJacobian d hn hμ (T j) r a x) +
      (∑ a, ∑ b, (quadraticRowFlux d T i a x * quadraticRowFlux d T j b x) *
        ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x a) r b) := by
  unfold quadraticAssembledEquation
  rw [flux_fin3]
  rfl

theorem quadraticAssembledEquation_drift_spec (i j : Fin n) (x : Space n) :
    (quadraticAssembledEquation d hn hμ T hC hM i j).drift x =
      mixedRowDrift (coordinateHessian d.potential x) (quadraticJacobianMatrix d hn hμ (T i) x)
        (quadraticJacobianMatrix d hn hμ (T j) x) (fun a => quadraticDatumRawDerivative d (T i) a x)
        (fun a => quadraticRowFlux d T i a x) (fun a => quadraticRowFlux d T j a x) +
      mixedRowDrift (coordinateHessian d.potential x) (quadraticJacobianMatrix d hn hμ (T j) x)
        (quadraticJacobianMatrix d hn hμ (T i) x) (fun a => quadraticDatumRawDerivative d (T j) a x)
        (fun a => quadraticRowFlux d T j a x) (fun a => quadraticRowFlux d T i a x) +
      mixedHessianDrift (coordinateHessian d.potential x) (sourceConnectionCurvature d x)
        (fun a b r => ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x a) r b)
        (quadraticJacobianMatrix d hn hμ (T i) x) (quadraticJacobianMatrix d hn hμ (T j) x)
        (fun a => quadraticRowFlux d T i a x) (fun a => quadraticRowFlux d T j a x) := by
  unfold quadraticAssembledEquation
  rw [drift_fin3]
  rfl

theorem quadraticAssembledEquation_drift_ae (i j : Fin n) :
    (quadraticAssembledEquation d hn hμ T hC hM i j).drift =ᵐ[potentialMeasure d.potential]
      actualQuadraticProductionRHS d hn hμ T i j := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source, d.third_symmetric_ae.filter_mono hac.ae_le] with x hx hN
  let H := coordinateHessian d.potential x
  let J := H⁻¹
  let U := actualQuadraticFluxMatrix d T x
  let Di := quadraticJacobianMatrix d hn hμ (T i) x
  let Dj := quadraticJacobianMatrix d hn hμ (T j) x
  let Nu := sourceThirdAlong d (fun a y => quadraticRowFlux d T i a y) x
  let Nv := sourceThirdAlong d (fun a y => quadraticRowFlux d T j a y) x
  have hJH : J * H = 1 := Matrix.nonsing_inv_mul H ((Matrix.isUnit_iff_isUnit_det _).mp hx.1.isUnit)
  have hi : actualQuadraticHessianFactor d hn hμ T i x = Di + J * Nu := by
    change J * (H * Di + Nu) = _
    rw [Matrix.mul_add, ← Matrix.mul_assoc, hJH, Matrix.one_mul]
  have hj : actualQuadraticHessianFactor d hn hμ T j x = Dj + J * Nv := by
    change J * (H * Dj + Nv) = _
    rw [Matrix.mul_add, ← Matrix.mul_assoc, hJH, Matrix.one_mul]
  have hW : (fun a => quadraticRowFlux d T i a x) ⬝ᵥ (H *ᵥ fun a => quadraticRowFlux d T j a x) =
      actualQuadraticGram d T x i j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, actualQuadraticGram,
      actualQuadraticFluxMatrix, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
  have hS : (fun a => quadraticRowFlux d T i a x) ⬝ᵥ
      (sourceConnectionCurvature d x *ᵥ fun a => quadraticRowFlux d T j a x) =
        (U * sourceTargetCurvature d x * U.transpose) i j + (J * Nu * J * Nv).trace := by
    change (U i) ⬝ᵥ ((sourceTargetCurvature d x + matrixTraceGram J (sourceThirdMatrix d x)) *ᵥ U j) = _
    rw [Matrix.add_mulVec, dotProduct_add]
    congr 1
    · calc
        _ = ∑ a, ∑ b, sourceTargetCurvature d x a b * U i a * U j b := by
          simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
        _ = _ := row_source_pair _ U i j
    · calc
        _ = ∑ a, ∑ b, matrixTraceGram J (sourceThirdMatrix d x) a b * U i a * U j b := by
          simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
        _ = _ := traceGram_bilinear J (sourceThirdMatrix d x) (U i) (U j)
  have hc : (∑ a, ∑ b, ∑ r, (J * sourceThirdMatrix d x a) r b *
      (Di a r * quadraticRowFlux d T j b x + quadraticRowFlux d T i a x * Dj b r)) =
        (Di * J * Nv).trace + (Dj * J * Nu).trace :=
    connection_cross_bilinear J Di Dj (sourceThirdMatrix d x) hN (U i) (U j)
  rw [quadraticAssembledEquation_drift_spec, assembled_drift_expansion _ _ _ _ hx.1.isHermitian.isSymm, hW, hS]
  change actualQuadraticRawForcing d T i j x - actualQuadraticGram d T x i j -
    ((U * sourceTargetCurvature d x * U.transpose) i j + (J * Nu * J * Nv).trace) - 2 * (Di * Dj).trace -
      (∑ a, ∑ b, ∑ r, (J * sourceThirdMatrix d x a) r b *
        (Di a r * quadraticRowFlux d T j b x + quadraticRowFlux d T i a x * Dj b r)) = _
  rw [hc]
  change _ = actualQuadraticRawForcing d T i j x - actualQuadraticGram d T x i j -
    ((U * sourceTargetCurvature d x * U.transpose) i j +
      (actualQuadraticHessianFactor d hn hμ T i x * actualQuadraticHessianFactor d hn hμ T j x).trace + (Di * Dj).trace)
  rw [hi, hj]
  have he := whole_row_completion J Nu Nv Di Dj
  dsimp only [actualQuadraticRawForcing]
  linarith only [he]

theorem quadraticAssembledEquation_flux_ae (i j : Fin n) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      (fun a => (quadraticAssembledEquation d hn hμ T hC hM i j).flux a x) =
        fun a => ∑ r, (coordinateHessian d.potential x)⁻¹ a r * quadraticGramRawDerivative d hn hμ T i j r x := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source, d.third_symmetric_ae.filter_mono hac.ae_le,
    (quadraticFluxJacobian_compatible_volume_ae d hn hμ (T i)).filter_mono hac.ae_le,
    (quadraticFluxJacobian_compatible_volume_ae d hn hμ (T j)).filter_mono hac.ae_le] with x hx hN hi hj
  have hJH := Matrix.nonsing_inv_mul (coordinateHessian d.potential x)
    ((Matrix.isUnit_iff_isUnit_det _).mp hx.1.isUnit)
  have hmetric := compatible_gram_metric_flux (coordinateHessian d.potential x)
    (coordinateHessian d.potential x)⁻¹ (sourceThirdMatrix d x) hx.1.isHermitian.isSymm hJH
    (fun r a b => (hN r a b).1) (fun a => quadraticRowFlux d T i a x) (fun a => quadraticRowFlux d T j a x)
    (quadraticJacobianMatrix d hn hμ (T i) x) (quadraticJacobianMatrix d hn hμ (T j) x) hi hj
  funext r
  rw [quadraticAssembledEquation_flux_spec]
  have hh := congrFun hmetric r
  change (∑ r', (coordinateHessian d.potential x)⁻¹ r r' * quadraticGramRawDerivative d hn hμ T i j r' x) = _ at hh
  rw [hh]
  have hconn : (∑ a, ∑ b, (quadraticRowFlux d T i a x * quadraticRowFlux d T j b x) *
      ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x a) r b) =
      (((coordinateHessian d.potential x)⁻¹ * sourceThirdAlong d (fun a y => quadraticRowFlux d T i a y) x) *ᵥ
        (fun a => quadraticRowFlux d T j a x)) r := by
    simp only [sourceThirdAlong, Matrix.mul_sum, Matrix.mul_smul, Matrix.mulVec, dotProduct,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
  rw [hconn]
  congr 2 <;> exact Finset.sum_congr rfl fun a _ => mul_comm _ _

theorem actual_quadratic_gram_rawMetricWeakEquation (i j : Fin n) :
    RawMetricWeakEquation d (quadraticGramLocalTest d hn hμ T hC hM i j)
      (actualQuadraticProductionRHS d hn hμ T i j) :=
  rawMetricWeakEquation_of_sourceLocalDivergence d (quadraticAssembledEquation d hn hμ T hC hM i j)
    (quadraticGramLocalTest d hn hμ T hC hM i j) _
    (quadraticAssembledEquation_flux_ae d hn hμ T hC hM i j)
    (quadraticAssembledEquation_drift_ae d hn hμ T hC hM i j)

end Fixed
end KLSConstantImprovement.ActualQuadraticGramCompactProduction405

#print axioms KLSConstantImprovement.ActualQuadraticGramCompactProduction405.quadraticAssembledEquation_drift_ae
#print axioms KLSConstantImprovement.ActualQuadraticGramCompactProduction405.quadraticAssembledEquation_flux_ae
#print axioms KLSConstantImprovement.ActualQuadraticGramCompactProduction405.actual_quadratic_gram_rawMetricWeakEquation

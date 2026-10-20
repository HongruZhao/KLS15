import KLSConstantImprovement.ActualQuadraticJacobianEnergy405
import KLSConstantImprovement.ActualQuadraticRowCurvature405
import KLSConstantImprovement.ActualResponseProductionAlgebra405
import KLSConstantImprovement.ActualQuadraticRowEquation405

/-! Literal whole-row production fields on the same chosen quadratic
natural inverses. This definition file contains no asserted production
PDE or unproved domain witness. The actual weak equation and global
H testing are proved by the companion domain/assembly files. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualQuadraticGramProduction405
open KLS ActualBoundedCanonicalSource ActualSourceQuadraticEta405 ActualQuadraticResponseField405
open ActualQuadraticJacobianEnergy405 ActualSourceNaturalHessian405 ActualQuadraticRowCurvature405
open ActualQuadraticHilbertMatrix405 ActualResponseProductionAlgebra405 ActualSourceCurvatureDomains405
open ActualQuadraticRowEquation405
variable {n : ℕ} {μ : Measure (Space n)}

def actualQuadraticHessianFactor (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  (coordinateHessian d.potential x)⁻¹ * naturalCanonicalHessian d (quadraticSourceDatum d (T i))
    (quadraticFluxJacobian d hn hμ (T i)) x

def actualQuadraticProduction (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  actualQuadraticFluxMatrix d T x * sourceTargetCurvature d x * (actualQuadraticFluxMatrix d T x).transpose +
    compatibleTraceGram (fun i => actualQuadraticHessianFactor d hn hμ T i x) +
      compatibleTraceGram (fun i => quadraticJacobianMatrix d hn hμ (T i) x)

def actualQuadraticProductionXi (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  (coordinateHessian d.potential x * actualQuadraticProduction d hn hμ T x).trace

def actualQuadraticRawForcing (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (x : Space n) : ℝ :=
  ∑ a, (quadraticDatumRawDerivative d (T i) a x * quadraticRowFlux d T j a x +
    quadraticRowFlux d T i a x * quadraticDatumRawDerivative d (T j) a x)

def actualQuadraticProductionRHS (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (x : Space n) : ℝ :=
  actualQuadraticRawForcing d T i j x - actualQuadraticGram d T x i j -
    actualQuadraticProduction d hn hμ T x i j

end KLSConstantImprovement.ActualQuadraticGramProduction405

#print axioms KLSConstantImprovement.ActualQuadraticGramProduction405.actualQuadraticHessianFactor
#print axioms KLSConstantImprovement.ActualQuadraticGramProduction405.actualQuadraticProduction

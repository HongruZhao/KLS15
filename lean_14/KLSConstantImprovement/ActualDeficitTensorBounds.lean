import ActualFourthCumulantSpectralDefect
import ActualCubicCreationBound
import CubicCreationAdjointAlgebra

/-! Original-law signed tensor contractions for the deficit-curvature route.
Every ordered index is retained. The signed trace square has only an upper
bound here; no positive-semidefinite matrix identification is assumed.
-/
noncomputable section
open MeasureTheory Matrix ProbabilityTheory
open scoped BigOperators
namespace KLSConstantImprovement.ActualDeficitTensorBounds
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise
variable {n : ℕ}
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

def tensorSquare (T : Array3 (Fin n)) : ℝ := square T
def fourthContraction (μ : Measure (Space n)) (T : Array3 (Fin n)) : ℝ :=
  ∑ i, ∑ a, ∑ b, T i a b*actualFourthCumulantFlat μ (T i) a b
def signedTraceSquare (μ : Measure (Space n)) (T : Array3 (Fin n)) : ℝ :=
  ∑ i, ∑ j, KLSBelow25.CubicCreation.annihilation (actualThirdCubicArray μ) T i j*
    KLSBelow25.CubicCreation.annihilation (actualThirdCubicArray μ) T j i
def sliceDeficit (μ : Measure (Space n)) (T : Array3 (Fin n)) : ℝ :=
  6*tensorSquare T-fourthContraction μ T

theorem tensorSquare_eq_sum_slices (T : Array3 (Fin n)) :
    tensorSquare T=∑ i,matrixFrobeniusSq (T i) := rfl

theorem fourthContraction_bounds {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT23 : ∀ i j k,T i j k=T i k j) :
    -2*tensorSquare T ≤ fourthContraction μ T ∧
      fourthContraction μ T ≤ 6*tensorSquare T := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hslice (i : Fin n) :
      -2*matrixFrobeniusSq (T i) ≤ ∑ a,∑ b,T i a b*actualFourthCumulantFlat μ (T i) a b ∧
      (∑ a,∑ b,T i a b*actualFourthCumulantFlat μ (T i) a b) ≤ 6*matrixFrobeniusSq (T i) := by
    have hsym:Matrix.IsSymm (T i) := by
      ext a b
      exact hT23 i b a
    rw [actualFourthCumulantFlat_pairing_eq_variance_sub_two hμ.quadraticVarianceEight_unconditional]
    have hv := (hμ.quadraticVarianceEight_unconditional (T i) hsym).2
    have hn := ProbabilityTheory.variance_nonneg (matrixQuadratic (T i)) μ
    constructor <;> linarith
  constructor
  · have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>(hslice i).1)
    simpa only [←Finset.mul_sum,←tensorSquare_eq_sum_slices,fourthContraction] using hs
  · have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>(hslice i).2)
    simpa only [←Finset.mul_sum,←tensorSquare_eq_sum_slices,fourthContraction] using hs

theorem sliceDeficit_nonneg {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT23 : ∀ i j k,T i j k=T i k j) : 0 ≤ sliceDeficit μ T := by
  exact sub_nonneg.mpr (fourthContraction_bounds hμ T hT23).2

theorem signedTraceSquare_le_sixteen_thirds {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) :
    signedTraceSquare μ T ≤ (16/3 : ℝ)*tensorSquare T :=
  KLSBelow25.CubicCreation.annihilation_trace_square_le (actualThirdCubicArray μ) T hT12 hT23
    (fun H hH=>actual_cubic_creation_square_le hμ H hH)

end KLSConstantImprovement.ActualDeficitTensorBounds
#print axioms KLSConstantImprovement.ActualDeficitTensorBounds.tensorSquare_eq_sum_slices
#print axioms KLSConstantImprovement.ActualDeficitTensorBounds.fourthContraction_bounds
#print axioms KLSConstantImprovement.ActualDeficitTensorBounds.sliceDeficit_nonneg
#print axioms KLSConstantImprovement.ActualDeficitTensorBounds.signedTraceSquare_le_sixteen_thirds

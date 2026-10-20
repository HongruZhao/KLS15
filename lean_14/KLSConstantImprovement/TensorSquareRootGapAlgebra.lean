import KLS.TensorCommutatorComparison
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Exact matrix and integral bookkeeping for a tensor square-root gap.
The root identity and common-kernel gap sign are explicit inputs. This
module does not assert the positive-map comparison or identify a kernel
of an arbitrary original law. No slot-response bound is inserted. -/
noncomputable section
open Matrix MeasureTheory
open scoped BigOperators
namespace KLSConstantImprovement.TensorSquareRootGapAlgebra
open KLS
variable {n : ℕ} {ι : Type*} [Fintype ι]

def tensorSandwich (T : ι → Matrix (Fin n) (Fin n) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ((H*T i)*(H*T i)).trace

def rootSandwich (A H : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ((H*A)*(H*A)).trace

def rootGap (A : Matrix (Fin n) (Fin n) ℝ)
    (T : ι → Matrix (Fin n) (Fin n) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  rootSandwich A H-tensorSandwich T H

def excessCommutator (A : Matrix (Fin n) (Fin n) ℝ)
    (T : ι → Matrix (Fin n) (Fin n) ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (∑ i,matrixFrobeniusSq (H*T i-T i*H))-matrixFrobeniusSq (H*A-A*H)

theorem excessCommutator_eq_twice_gap
    (A H : Matrix (Fin n) (Fin n) ℝ) (T : ι → Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (hH : H.IsSymm) (hT : ∀ i,(T i).IsSymm)
    (hroot : A*A=∑ i,T i*T i) :
    excessCommutator A T H=2*rootGap A T H := by
  have hs : (∑ i,(((H*H)*(T i*T i)).trace-((H*T i)*(H*T i)).trace))=
      (1/2 : ℝ)*(∑ i,matrixFrobeniusSq (H*T i-T i*H)) := by
    simp_rw [matrix_trace_commutator_difference H _ hH (hT _)]
    rw [Finset.mul_sum]
  have hr : (∑ i,((H*H)*(T i*T i)).trace)=((H*H)*(A*A)).trace := by
    rw [←Matrix.trace_sum,←Finset.mul_sum,←hroot]
  rw [Finset.sum_sub_distrib,hr] at hs
  have ha := matrix_trace_commutator_difference H A hH hA
  dsimp [excessCommutator,rootGap,rootSandwich,tensorSandwich]
  linarith

theorem normalized_gap_budget {N EA ST d : ℝ}
    (hA : 0 ≤ 2*N-EA) (hgap : 0 ≤ EA-ST) (hd : 4*(2*N-ST) ≤ d) :
    0 ≤ EA-ST ∧ EA-ST ≤ d/4 ∧
      2*N-EA ≤ 2*N-ST ∧ 2*N-ST ≤ d/4 := by
  constructor
  · exact hgap
  constructor
  · linarith
  constructor <;> linarith

theorem integral_gap_eq_difference {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (A : Matrix (Fin n) (Fin n) ℝ) (T : ι → Matrix (Fin n) (Fin n) ℝ)
    (H : X → Matrix (Fin n) (Fin n) ℝ)
    (hA : Integrable (fun x => rootSandwich A (H x)) μ)
    (hT : Integrable (fun x => tensorSandwich T (H x)) μ) :
    (∫ x,rootGap A T (H x) ∂μ)=
      (∫ x,rootSandwich A (H x) ∂μ)-(∫ x,tensorSandwich T (H x) ∂μ) := by
  exact integral_sub hA hT

theorem common_kernel_gap_and_commutator_budget {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (A : Matrix (Fin n) (Fin n) ℝ)
    (T : ι → Matrix (Fin n) (Fin n) ℝ) (H : X → Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (hT : ∀ i,(T i).IsSymm) (hH : ∀ x,(H x).IsSymm)
    (hroot : A*A=∑ i,T i*T i)
    (hrootInt : Integrable (fun x => rootSandwich A (H x)) μ)
    (htensorInt : Integrable (fun x => tensorSandwich T (H x)) μ)
    (hgap : ∀ x,0 ≤ rootGap A T (H x)) (N d : ℝ)
    (hdeltaA : 0 ≤ 2*N-(∫ x,rootSandwich A (H x) ∂μ))
    (hd : 4*(2*N-(∫ x,tensorSandwich T (H x) ∂μ)) ≤ d) :
    0 ≤ (∫ x,rootGap A T (H x) ∂μ) ∧
      (∫ x,rootGap A T (H x) ∂μ) ≤ d/4 ∧
        (∫ x,excessCommutator A T (H x) ∂μ) ≤ d/2 := by
  have hg : 0 ≤ (∫ x,rootGap A T (H x) ∂μ) := integral_nonneg hgap
  have he := integral_gap_eq_difference μ A T H hrootInt htensorInt
  have hp := normalized_gap_budget hdeltaA (by linarith [hg,he]) hd
  have hc : (fun x => excessCommutator A T (H x))=(fun x => 2*rootGap A T (H x)) := by
    funext x
    exact excessCommutator_eq_twice_gap A (H x) T hA (hH x) hT hroot
  have hi : (∫ x,excessCommutator A T (H x) ∂μ)=2*(∫ x,rootGap A T (H x) ∂μ) := by
    rw [hc,integral_const_mul]
  exact ⟨hg,by linarith [hp.2.1,he],by linarith [hp.2.1,he,hi]⟩

end KLSConstantImprovement.TensorSquareRootGapAlgebra
#print axioms KLSConstantImprovement.TensorSquareRootGapAlgebra.excessCommutator_eq_twice_gap
#print axioms KLSConstantImprovement.TensorSquareRootGapAlgebra.normalized_gap_budget
#print axioms KLSConstantImprovement.TensorSquareRootGapAlgebra.integral_gap_eq_difference
#print axioms KLSConstantImprovement.TensorSquareRootGapAlgebra.common_kernel_gap_and_commutator_budget

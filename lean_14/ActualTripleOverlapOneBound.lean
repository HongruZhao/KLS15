import ActualFourthCumulantSymmetry
import TripleTensorOverlapOneAlgebra

/-! Genuine overlap-one bound for unordered-triple fourth-cumulant insertion.
The only analytic input is the actual two-to-two flat norm at most six. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLSBelow25.PairTensor
variable {n r : ℕ}
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem symmetric_tensor_quadratic_slice (H : Tensor (ι:=Fin n) (r+3))
    (hH : Symmetric H) (b : Fin n) (z : Fin r→Fin n) :
    Matrix.IsSymm (fun j k=>H (Fin.cons b (Fin.cons j (Fin.cons k z)))) := by
  ext j k
  have hh := symmetric_cons_tail H hH (Equiv.swap (0 : Fin (r+2)) 1) b
    (Fin.cons j (Fin.cons k z))
  rw [cons_two_exchangeSwap] at hh
  exact hh

/-- True triple-insertion ONE-overlap cap. It is distinct from the
one-to-three diagonal cap and the TWO-overlap cap. -/
theorem actual_triple_overlap_one_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (H : Tensor (ι:=Fin n) (r+3)) (hH : Symmetric H) :
    pairing (KLSBelow25.TripleTensor.kernelInFrame (actualFourthCumulantArray μ) H
        (KLSBelow25.TripleTensor.consFrame (r+2)))
      (fun a=>KLSBelow25.TripleTensor.kernelInFrame (actualFourthCumulantArray μ) H
        (KLSBelow25.TripleTensor.consFrame (r+2))
        (a∘KLSBelow25.TripleTensor.overlapOneSwap r)) ≤ 36*square H := by
  let M := fun (z : Fin r→Fin n) (i a b : Fin n)=>
    ∑ j,∑ k,actualFourthCumulantArray μ i a j k*
      H (Fin.cons b (Fin.cons j (Fin.cons k z)))
  have hflat (z : Fin r→Fin n) (b : Fin n) :
      (∑ i,∑ a,(M z i a b)^2) ≤
        36*(∑ j,∑ k,H (Fin.cons b (Fin.cons j (Fin.cons k z)))^2) := by
    exact actual_fourth_cumulant_tensor_flat_square_le hμ _
      (symmetric_tensor_quadratic_slice H hH b z)
  rw [KLSBelow25.TripleTensor.overlap_one_pairing_eq_exchange,Finset.sum_comm]
  simp_rw [actualFourthCumulant_last_to_second hμ]
  change (∑ z,∑ i,∑ a,∑ b,M z i a b*M z i b a) ≤ _
  calc
    _ ≤ ∑ z,∑ i,∑ a,∑ b,(M z i a b)^2 := by
      exact Finset.sum_le_sum fun z _=>Finset.sum_le_sum fun i _=>
        KLSBelow25.TripleTensor.matrix_exchange_le_square (M z i)
    _ = ∑ z,∑ b,∑ i,∑ a,(M z i a b)^2 := by
      apply Finset.sum_congr rfl
      intro z _
      conv_lhs =>
        arg 2;ext i
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ ≤ ∑ z,∑ b,36*(∑ j,∑ k,H (Fin.cons b (Fin.cons j (Fin.cons k z)))^2) :=
      Finset.sum_le_sum fun z _=>Finset.sum_le_sum fun b _=>hflat z b
    _ = 36*square H := by
      simp only [←Finset.mul_sum]
      congr 1
      unfold square
      conv_rhs =>
        rw [sum_cons_coordinates]
        arg 2;ext b
        rw [sum_cons_coordinates]
        arg 2;ext j
        rw [sum_cons_coordinates]
      conv_rhs =>
        arg 2;ext b
        arg 2;ext j
        rw [Finset.sum_comm]
      conv_rhs =>
        arg 2;ext b
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actual_triple_overlap_one_le

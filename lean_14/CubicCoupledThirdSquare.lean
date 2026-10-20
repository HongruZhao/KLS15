import Mathlib

/-! An exact algebraic obstruction to a proposed cubic-cap reduction.

The tensor below satisfies scalar skewness, total-trace, and distinct-slot
matrix bounds, but violates the coupled third-cumulant square bound four.
No log-concave realization of this abstract tensor is asserted. In
particular this is not a counterexample to the universal cubic cap six.
The mathematical proof was saved first in
research/cubic-cap-coupled-third-square-audit.md. -/
noncomputable section
open scoped BigOperators
namespace KLSImprovement.CoupledThirdSquare
set_option maxHeartbeats 2000000

abbrev BinaryCubic := Fin 4 → ℝ

/-- Ordered symmetric tensor entry, indexed by the number of second indices. -/
def entry (c : BinaryCubic) (i j k : Fin 2) : ℝ :=
  c ⟨i.val+j.val+k.val, by
    have hi := i.isLt
    have hj := j.isLt
    have hk := k.isLt
    omega⟩

def tensorNormSq (c : BinaryCubic) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, (entry c i j k)^2

def scalarCubic (c : BinaryCubic) (x y : ℝ) : ℝ :=
  c 0*x^3+3*c 1*x^2*y+3*c 2*x*y^2+c 3*y^3

def contraction (t c : BinaryCubic) (k l : Fin 2) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, entry t i j k*entry c i j l

def coupledSquare (t c : BinaryCubic) : ℝ :=
  ∑ k : Fin 2, ∑ l : Fin 2, contraction t c k l*contraction t c l k

/-- The ordinary trace sum tr(B C_k B C_k), for B=[[p,q],[q,r]]. -/
def distinctSlotSquare (c : BinaryCubic) (p q r : ℝ) : ℝ :=
  let b : Fin 2 → Fin 2 → ℝ := ![![p,q],![q,r]]
  ∑ k : Fin 2, ∑ i : Fin 2, ∑ a : Fin 2,
    ∑ j : Fin 2, ∑ d : Fin 2,
      b i a*entry c a j k*b j d*entry c d i k

theorem tensorNormSq_eq (c : BinaryCubic) :
    tensorNormSq c = (c 0)^2+3*(c 1)^2+3*(c 2)^2+(c 3)^2 := by
  simp [tensorNormSq, entry, Fin.sum_univ_two]
  ring

theorem scalarCubic_eq_ordered_contraction (c : BinaryCubic) (x y : ℝ) :
    scalarCubic c x y =
      ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2,
        entry c i j k*(![x,y] i)*(![x,y] j)*(![x,y] k) := by
  simp [scalarCubic, entry, Fin.sum_univ_two]
  ring

def obstructionTensor : BinaryCubic := ![8/5,-4/5,-4/5,16/25]
def witnessTensor : BinaryCubic := ![-5,2,1,-1]

theorem obstruction_scalar_sos (x y : ℝ) :
    625*(4*(x^2+y^2)^3-(scalarCubic obstructionTensor x y)^2) =
      900*(x^3+(8/3 : ℝ)*x^2*y-(53/30 : ℝ)*x*y^2)^2+
      5480*(x^2*y)^2+
      3011*(x*y^2+(960/3011 : ℝ)*y^3)^2+
      (5835084/3011 : ℝ)*(y^3)^2 := by
  norm_num [scalarCubic, obstructionTensor]
  ring

theorem obstruction_scalar_skewness (x y : ℝ) :
    (scalarCubic obstructionTensor x y)^2 ≤ 4*(x^2+y^2)^3 := by
  have h := obstruction_scalar_sos x y
  have hn : 0 ≤
      900*(x^3+(8/3 : ℝ)*x^2*y-(53/30 : ℝ)*x*y^2)^2+
      5480*(x^2*y)^2+
      3011*(x*y^2+(960/3011 : ℝ)*y^3)^2+
      (5835084/3011 : ℝ)*(y^3)^2 := by positivity
  linarith

theorem obstruction_trace_bound : tensorNormSq obstructionTensor < 8 := by
  rw [tensorNormSq_eq]
  norm_num [obstructionTensor]

theorem obstruction_distinct_slot_sos (p q r : ℝ) :
    625*(4*(p^2+2*q^2+r^2)-distinctSlotSquare obstructionTensor p q r) =
      500*(p+(8/5 : ℝ)*q-(8/5 : ℝ)*r)^2+
      4360*(q+(28/109 : ℝ)*r)^2+(30116/109 : ℝ)*r^2 := by
  norm_num [distinctSlotSquare, entry, obstructionTensor, Fin.sum_univ_two]
  ring

theorem obstruction_distinct_slot_bound (p q r : ℝ) :
    distinctSlotSquare obstructionTensor p q r ≤ 4*(p^2+2*q^2+r^2) := by
  have h := obstruction_distinct_slot_sos p q r
  have hn : 0 ≤ 500*(p+(8/5 : ℝ)*q-(8/5 : ℝ)*r)^2+
      4360*(q+(28/109 : ℝ)*r)^2+(30116/109 : ℝ)*r^2 := by positivity
  linarith

theorem exact_witness_norm : tensorNormSq witnessTensor = 41 := by
  rw [tensorNormSq_eq]
  norm_num [witnessTensor]

theorem exact_coupled_excess :
    coupledSquare witnessTensor obstructionTensor-
      4*tensorNormSq witnessTensor = (1036/625 : ℝ) := by
  norm_num [coupledSquare, contraction, tensorNormSq, entry,
    obstructionTensor, witnessTensor, Fin.sum_univ_two]

theorem obstruction_violates_coupled_four :
    4*tensorNormSq witnessTensor < coupledSquare witnessTensor obstructionTensor := by
  have h := exact_coupled_excess
  linarith

/-- These three necessary moment constraints do not algebraically imply
the coupled bound. There is no probability-law assertion in this theorem. -/
theorem known_constraints_do_not_imply_coupled_four :
    ∃ c : BinaryCubic,
      (∀ x y : ℝ, (scalarCubic c x y)^2 ≤ 4*(x^2+y^2)^3) ∧
      tensorNormSq c ≤ 8 ∧
      (∀ p q r : ℝ, distinctSlotSquare c p q r ≤ 4*(p^2+2*q^2+r^2)) ∧
      ∃ t : BinaryCubic, 4*tensorNormSq t < coupledSquare t c := by
  exact ⟨obstructionTensor, obstruction_scalar_skewness,
    obstruction_trace_bound.le, obstruction_distinct_slot_bound,
    witnessTensor, obstruction_violates_coupled_four⟩

end KLSImprovement.CoupledThirdSquare
#print axioms KLSImprovement.CoupledThirdSquare.scalarCubic_eq_ordered_contraction
#print axioms KLSImprovement.CoupledThirdSquare.obstruction_scalar_skewness
#print axioms KLSImprovement.CoupledThirdSquare.obstruction_distinct_slot_bound
#print axioms KLSImprovement.CoupledThirdSquare.exact_coupled_excess
#print axioms KLSImprovement.CoupledThirdSquare.known_constraints_do_not_imply_coupled_four

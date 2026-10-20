import Mathlib

/-! Finite cancellations in the variable-skew source response cost.
The compact source IBP/domain and cost identification remain analytic
inputs; no numerical cost or higher source-gap bound is asserted. -/
noncomputable section
namespace KLSConstantImprovement.OriginalVariableSkewResponseCost
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem third_skew_metric_contraction_zero
    (N : ι → ι → ι → ℝ) (A : ι → ι → ℝ)
    (hN : ∀ i a b, N i a b = N b a i)
    (hA : ∀ b i, A b i = -A i b) (a : ι) :
    (∑ i, ∑ b, N i a b*A b i)=0 := by
  have hp : ∀ i b, N i a b*A b i = -(N b a i*A i b) := by
    intro i b
    rw [hN i a b, hA b i]
    ring
  have hr : (∑ i, ∑ b, N i a b*A b i) =
      -(∑ i, ∑ b, N b a i*A i b) := by
    calc
      (∑ i, ∑ b, N i a b*A b i) =
          ∑ i, ∑ b, -(N b a i*A i b) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro b hb
        exact hp i b
      _ = -(∑ i, ∑ b, N b a i*A i b) := by
        simp only [Finset.sum_neg_distrib]
  have hc : (∑ i, ∑ b, N b a i*A i b) =
      (∑ b, ∑ i, N b a i*A i b) := Finset.sum_comm
  linarith

theorem derivative_skew_metric_contraction_zero
    (N : ι → ι → ι → ℝ) (D : ι → ι → ι → ℝ)
    (hN : ∀ i a b, N i a b = N b a i)
    (hD : ∀ k b i, D k b i = -D k i b) (k a : ι) :
    (∑ i, ∑ b, N i a b*D k b i)=0 := by
  exact third_skew_metric_contraction_zero N (D k) hN (hD k) a

theorem variable_skew_norm_budget {Q a0 a1 a2 a3 : ℝ}
    (hQ : Q=a0+a1+a2+a3) (h2 : a2=0) (h3 : a3=0) :
    Q=a0+a1 := by linarith

theorem closed_derivative_swap_can_be_negative :
    (-2:ℝ)+1+1=0 ∧ (-2:ℝ)*16+4*1+4*1=-24 ∧
    (-24:ℝ)<0 := by norm_num

end KLSConstantImprovement.OriginalVariableSkewResponseCost
#print axioms KLSConstantImprovement.OriginalVariableSkewResponseCost.third_skew_metric_contraction_zero
#print axioms KLSConstantImprovement.OriginalVariableSkewResponseCost.derivative_skew_metric_contraction_zero
#print axioms KLSConstantImprovement.OriginalVariableSkewResponseCost.variable_skew_norm_budget
#print axioms KLSConstantImprovement.OriginalVariableSkewResponseCost.closed_derivative_swap_can_be_negative

import Mathlib

/-! Cost recurrence and moment normalization for signed higher-order kernels.
The gradient-closure/adjoint construction and cutoff identities stay explicit
analytic inputs; these scalar consequences do not prove existence of a field. -/
noncomputable section
namespace KLSConstantImprovement.HigherOrderKernelCostScalar

theorem repeated_adjoint_cost {C h : ℝ} (hC : 0 ≤ C) (cost : ℕ→ℝ)
    (hzero : cost 0 ≤ h) (hstep : ∀ q, cost (q+1) ≤ C*cost q) :
    ∀ q, cost q ≤ C^q*h := by
  intro q
  induction q with
  | zero => simpa using hzero
  | succ q ih =>
    calc
      cost (q+1) ≤ C*cost q := hstep q
      _ ≤ C*(C^q*h) := mul_le_mul_of_nonneg_left ih hC
      _ = C^(q+1)*h := by rw [pow_succ];ring

theorem symmetrized_adjoint_cost {C h U : ℝ} (hC : 0 ≤ C) (cost : ℕ→ℝ)
    (hzero : cost 0 ≤ h) (hstep : ∀ q, cost (q+1) ≤ C*cost q)
    (r : ℕ) (hsym : U ≤ cost r) : U ≤ C^r*h :=
  hsym.trans (repeated_adjoint_cost hC cost hzero hstep r)

theorem second_order_signed_cost {C h F U : ℝ} (hC : 0 ≤ C)
    (hfirst : F ≤ C*h) (hsecond : U ≤ C*F) : U ≤ C^2*h := by
  have h:=mul_le_mul_of_nonneg_left hfirst hC
  nlinarith

theorem normalized_lower_moment_vanishes {r : ℕ} {moment mean : ℝ}
    (hpair : (r.factorial:ℝ)*mean=moment) (horth : moment=0) : mean=0 := by
  have hf:(r.factorial:ℝ)≠0 := by exact_mod_cast r.factorial_ne_zero
  rw [horth] at hpair
  exact (mul_eq_zero.mp hpair).resolve_left hf

theorem normalized_kernel_mean {r : ℕ} {moment mean : ℝ}
    (hpair : (r.factorial:ℝ)*mean=moment) : mean=moment/(r.factorial:ℝ) := by
  have hf:(r.factorial:ℝ)≠0 := by exact_mod_cast r.factorial_ne_zero
  apply (eq_div_iff hf).mpr
  simpa [mul_comm] using hpair

end KLSConstantImprovement.HigherOrderKernelCostScalar
#print axioms KLSConstantImprovement.HigherOrderKernelCostScalar.repeated_adjoint_cost
#print axioms KLSConstantImprovement.HigherOrderKernelCostScalar.symmetrized_adjoint_cost
#print axioms KLSConstantImprovement.HigherOrderKernelCostScalar.second_order_signed_cost
#print axioms KLSConstantImprovement.HigherOrderKernelCostScalar.normalized_lower_moment_vanishes
#print axioms KLSConstantImprovement.HigherOrderKernelCostScalar.normalized_kernel_mean

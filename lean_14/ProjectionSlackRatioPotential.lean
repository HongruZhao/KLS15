import Mathlib

/-! Finite scalar identities for the genuine projection-slack orbit.
These retain the next-step slack and do not assert a discounted endpoint. -/
noncomputable section
namespace KLSBelow25.ProjectionSlackRatio

/-- The finite terminal slack is part of the corrected ratio potential. -/
theorem corrected_potential_step
    (eta w rho rhoNext d a aNext : ℝ)
    (hrec : rhoNext = rho-d+a)
    (hpay : eta*d ≤ w*a+(1-w)*aNext) :
    rho+(1-w)*a-(1-eta)*d ≤ rhoNext+(1-w)*aNext := by
  rw [hrec]
  nlinarith

/-- Exact factorization behind two-step compensation of a downward ratio. -/
theorem two_step_factorization (w r rho : ℝ) (hw : w ≠ 1) :
    rho*((r-w*rho)/(1-w))-r^2 =
      (r-rho)*(w*rho-(1-w)*r)/(1-w) := by
  field_simp
  ring

/-- A downward step in the valid interval is repaid by its successor,
with its actual cost retained. -/
theorem two_step_product_with_cost
    (w r rho rhoNext d : ℝ) (hw0 : 0 < w) (hw1 : w < 1)
    (hrho0 : 0 ≤ rho) (hrho : rho ≤ r)
    (hlower : (1-w)*r/w ≤ rho)
    (hnext : (r-w*rho)/(1-w)-d ≤ rhoNext) :
    r^2-rho*d ≤ rho*rhoNext := by
  have hden : 0 < 1-w := sub_pos.mpr hw1
  have hleft : 0 ≤ r-rho := sub_nonneg.mpr hrho
  have hright : 0 ≤ w*rho-(1-w)*r := by
    have h := (div_le_iff₀ hw0).mp hlower
    nlinarith
  have hprod : 0 ≤ (r-rho)*(w*rho-(1-w)*r)/(1-w) :=
    div_nonneg (mul_nonneg hleft hright) hden.le
  rw [←two_step_factorization w r rho (ne_of_lt hw1)] at hprod
  have hm := mul_le_mul_of_nonneg_left hnext hrho0
  nlinarith

/-- If the corrected potential is at least r, the next ratio meets the
exact affine lower bound used in the product lemma. -/
theorem next_ratio_of_corrected_potential
    (w r rho rhoNext d a : ℝ) (hw1 : w < 1)
    (hrec : rhoNext = rho-d+a)
    (hpotential : r ≤ rho+(1-w)*a) :
    (r-w*rho)/(1-w)-d ≤ rhoNext := by
  apply (sub_le_iff_le_add).mpr
  apply (div_le_iff₀ (sub_pos.mpr hw1)).mpr
  rw [hrec]
  nlinarith

/-- Exact finite telescoping. The final slack is deliberately retained. -/
theorem corrected_potential_finite
    (eta w : ℝ) (rho d a : ℕ → ℝ)
    (hrec : ∀ m, rho (m+1)=rho m-d m+a m)
    (hpay : ∀ m, eta*d m ≤ w*a m+(1-w)*a (m+1)) (N : ℕ) :
    rho 0+(1-w)*a 0-(1-eta)*(∑ m∈Finset.range N,d m) ≤
      rho N+(1-w)*a N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hh := corrected_potential_step eta w (rho N) (rho (N+1))
      (d N) (a N) (a (N+1)) (hrec N) (hpay N)
    nlinarith

/-- The two finite ingredients combine without discarding a cost. -/
theorem corrected_potential_two_step
    (w r rho rhoNext d a : ℝ) (hw0 : 0 < w) (hw1 : w < 1)
    (hrho0 : 0 ≤ rho) (hrho : rho ≤ r)
    (hlower : (1-w)*r/w ≤ rho)
    (hrec : rhoNext=rho-d+a)
    (hpotential : r ≤ rho+(1-w)*a) :
    r^2-rho*d ≤ rho*rhoNext :=
  two_step_product_with_cost w r rho rhoNext d hw0 hw1 hrho0 hrho hlower
    (next_ratio_of_corrected_potential w r rho rhoNext d a hw1 hrec hpotential)

end KLSBelow25.ProjectionSlackRatio
#print axioms KLSBelow25.ProjectionSlackRatio.corrected_potential_step
#print axioms KLSBelow25.ProjectionSlackRatio.two_step_factorization
#print axioms KLSBelow25.ProjectionSlackRatio.two_step_product_with_cost
#print axioms KLSBelow25.ProjectionSlackRatio.next_ratio_of_corrected_potential

#print axioms KLSBelow25.ProjectionSlackRatio.corrected_potential_finite
#print axioms KLSBelow25.ProjectionSlackRatio.corrected_potential_two_step

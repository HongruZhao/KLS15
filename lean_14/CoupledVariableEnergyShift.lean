import CoupledEnergyShift

/-! Rank-dependent nonnegative generator parameters shift with the
factorial weights. The quadratic head has no incoming positive term. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.CoupledEnergy

theorem variable_factorial_weight_energy_shift
    (E beta : ℕ → ℝ) {K : ℝ} (hK : 0<K)
    (hbeta : ∀ d,2 ≤ d → 0 ≤ beta d) (hE : ∀ d,0 ≤ E d)
    (N : ℕ) (hN : 2 ≤ N) :
    (∑ d ∈ Finset.Icc 3 N,
      K*beta (d-1)*(d : ℝ)^2*factorialWeight K d*E d) ≤
    ∑ d ∈ Finset.Icc 2 N,beta d*factorialWeight K d*E (d+1) := by
  classical
  have hshift : (∑ d ∈ Finset.Icc 2 N,beta d*factorialWeight K d*E (d+1))=
      ∑ d ∈ Finset.Icc 3 (N+1),beta (d-1)*factorialWeight K (d-1)*E d := by
    apply Finset.sum_bij (fun d _ => d+1)
    · intro d hd
      simp only [Finset.mem_Icc] at hd ⊢
      omega
    · intro a ha b hb he
      omega
    · intro d hd
      simp only [Finset.mem_Icc] at hd
      refine ⟨d-1,?_,?_⟩
      · simp only [Finset.mem_Icc]; omega
      · omega
    · intro d hd
      simp
  have htail : (∑ d ∈ Finset.Icc 3 N,
      K*beta (d-1)*(d : ℝ)^2*factorialWeight K d*E d)=
      ∑ d ∈ Finset.Icc 3 N,beta (d-1)*factorialWeight K (d-1)*E d := by
    apply Finset.sum_congr rfl
    intro d hd
    have hd1 : d-1+1=d := by have := (Finset.mem_Icc.mp hd).1; omega
    rw [factorialWeight_step hK (d-1),hd1]
    ring
  rw [htail,hshift]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    simp only [Finset.mem_Icc] at hd ⊢
    omega
  · intro d hd hnot
    have hd3 : 3 ≤ d := (Finset.mem_Icc.mp hd).1
    exact mul_nonneg (mul_nonneg (hbeta _ (by omega)) (factorialWeight_nonneg hK _)) (hE _)

end KLSBelow25.CoupledEnergy
#print axioms KLSBelow25.CoupledEnergy.variable_factorial_weight_energy_shift

import Mathlib

/-! The factorial weighted energy shift, with the missing rank-two
incoming term explicitly subtracted. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.CoupledEnergy

def factorialWeight (K : ℝ) (d : ℕ) : ℝ := (K^d*(d.factorial : ℝ)^2)⁻¹

theorem factorialWeight_nonneg {K : ℝ} (hK : 0<K) (d : ℕ) :
    0 ≤ factorialWeight K d := by unfold factorialWeight; positivity

theorem factorialWeight_step {K : ℝ} (hK : 0<K) (d : ℕ) :
    factorialWeight K d=K*((d+1 : ℕ) : ℝ)^2*factorialWeight K (d+1) := by
  have hf : (d.factorial : ℝ) ≠ 0 := by positivity
  have hd : ((d+1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold factorialWeight
  rw [Nat.factorial_succ,Nat.cast_mul,pow_succ]
  field_simp
  ring

theorem factorial_weight_energy_shift
    (E : ℕ → ℝ) {K : ℝ} (hK : 0<K) (hE : ∀ d,0≤E d)
    (N : ℕ) (hN : 2≤N) :
    K*(∑d∈Finset.Icc 2 N,(d : ℝ)^2*factorialWeight K d*E d)-
      4*K*factorialWeight K 2*E 2 ≤
    ∑d∈Finset.Icc 2 N,factorialWeight K d*E (d+1) := by
  classical
  have hset : Finset.Icc 2 N=insert 2 (Finset.Icc 3 N) := by
    ext d
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  have hnot : 2∉Finset.Icc 3 N := by simp
  have hshift : (∑d∈Finset.Icc 2 N,factorialWeight K d*E (d+1))=
      ∑d∈Finset.Icc 3 (N+1),factorialWeight K (d-1)*E d := by
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
  have he : K*(∑d∈Finset.Icc 2 N,(d : ℝ)^2*factorialWeight K d*E d)-
      4*K*factorialWeight K 2*E 2=
      ∑d∈Finset.Icc 3 N,factorialWeight K (d-1)*E d := by
    rw [hset,Finset.sum_insert hnot]
    simp only [Nat.cast_ofNat]
    rw [mul_add]
    have hw : (∑d∈Finset.Icc 3 N,factorialWeight K (d-1)*E d)=
        K*(∑d∈Finset.Icc 3 N,(d : ℝ)^2*factorialWeight K d*E d) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      have hd1 : d-1+1=d := by have := (Finset.mem_Icc.mp hd).1; omega
      rw [factorialWeight_step hK (d-1),hd1]
      ring
    rw [hw]
    ring
  rw [he,hshift]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    simp only [Finset.mem_Icc] at hd ⊢
    omega
  · intro d hd hnot
    exact mul_nonneg (factorialWeight_nonneg hK _) (hE _)

theorem scaled_factorial_weight_energy_shift
    (E : ℕ → ℝ) {K alpha : ℝ} (hK : 0<K) (halpha : 0≤alpha)
    (hE : ∀ d,0≤E d) (N : ℕ) (hN : 2≤N) :
    alpha*K*(∑d∈Finset.Icc 2 N,(d : ℝ)^2*factorialWeight K d*E d)-
      4*alpha*K*factorialWeight K 2*E 2 ≤
    alpha*(∑d∈Finset.Icc 2 N,factorialWeight K d*E (d+1)) := by
  have h := mul_le_mul_of_nonneg_left (factorial_weight_energy_shift E hK hE N hN) halpha
  nlinarith [h]

end KLSBelow25.CoupledEnergy
#print axioms KLSBelow25.CoupledEnergy.factorial_weight_energy_shift

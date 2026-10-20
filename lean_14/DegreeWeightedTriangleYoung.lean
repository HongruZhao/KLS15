import ExactTriangleDriftYoung

/-! Degree-dependent Young weights preserve the genuine summed Bessel budget.
The weight is attached to the second contraction degree, not the Appell
degree of the tensor being contracted. No individual coefficient estimate
is substituted for the joint square-sum hypothesis. -/
noncomputable section
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem coupled_triangle_second_factor_weighted (N : ℕ) (P : ℕ → ℝ)
    (Q : ℕ → ℕ → ℝ) (v : ℕ → ℝ)
    {C : ℝ} (hv : ∀ b∈Finset.Icc 2 N,0≤v b)
    (hjoint : ∀ b∈Finset.Icc 2 N,
      (∑ a∈Finset.Icc 2 (N-1),(Q a b)^2)≤C*(P b)^2) :
    (∑ p∈coupledDriftPairs N,v (p.1-p.2+1)*(Q p.2 (p.1-p.2+1))^2)≤
      ∑ b∈Finset.Icc 2 N,v b*C*(P b)^2 := by
  classical
  let e : (Σ _ : ℕ, ℕ) → ℕ × ℕ := fun p => (p.2,p.1-p.2+1)
  have hinj : Set.InjOn e (coupledDriftPairs N : Set (Σ _ : ℕ, ℕ)) := by
    intro p hp q hq he
    have hp' := Finset.mem_sigma.mp hp
    have hq' := Finset.mem_sigma.mp hq
    have ha := congrArg Prod.fst he
    have hb := congrArg Prod.snd he
    simp only [e] at ha hb
    apply Sigma.ext
    · have hp2 := Finset.mem_Icc.mp hp'.2
      have hq2 := Finset.mem_Icc.mp hq'.2
      omega
    · simpa only [heq_eq_eq] using ha
  have hsub : (coupledDriftPairs N).image e ⊆
      (Finset.Icc 2 (N-1)).product (Finset.Icc 2 N) := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hd,ha⟩ := Finset.mem_sigma.mp hq
    simp only [Finset.mem_Icc] at hd ha
    rw [Finset.product_eq_sprod]
    simp only [e,Finset.mem_product,Finset.mem_Icc]
    omega
  calc
    _ = ∑ p∈(coupledDriftPairs N).image e,v p.2*(Q p.1 p.2)^2 :=
      (Finset.sum_image hinj).symm
    _ ≤ ∑ p∈(Finset.Icc 2 (N-1)).product (Finset.Icc 2 N),v p.2*(Q p.1 p.2)^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro p hp hn
        exact mul_nonneg (hv p.2 (Finset.mem_product.mp hp).2) (sq_nonneg _))
    _ = ∑ b∈Finset.Icc 2 N,v b*(∑ a∈Finset.Icc 2 (N-1),(Q a b)^2) := by
      rw [Finset.product_eq_sprod,Finset.sum_product,Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum (fun b hb => by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hjoint b hb) (hv b hb))

theorem coupled_triangle_weighted_young (N : ℕ) (P : ℕ → ℝ)
    (Q : ℕ → ℕ → ℝ) (s : ℕ → ℝ) {C K : ℝ}
    (hK : 0≤K) (hs : ∀ b∈Finset.Icc 2 N,0<s b)
    (hjoint : ∀ b∈Finset.Icc 2 N,
      (∑ a∈Finset.Icc 2 (N-1),(Q a b)^2)≤C*(P b)^2) :
    2*Real.sqrt K*(∑ d∈Finset.Icc 3 N,∑ a∈Finset.Icc 2 (d-1),
      (P d/(d : ℝ))*Q a (d-a+1))≤
      (∑ d∈Finset.Icc 3 N,(∑ a∈Finset.Icc 2 (d-1),s (d-a+1))*
        (P d/(d : ℝ))^2)+
      ∑ b∈Finset.Icc 2 N,(K*C/s b)*(P b)^2 := by
  classical
  have hp : ∀ p∈coupledDriftPairs N,p.1-p.2+1∈Finset.Icc 2 N := by
    intro p hp
    obtain ⟨hd,ha⟩ := Finset.mem_sigma.mp hp
    simp only [Finset.mem_Icc] at hd ha ⊢
    omega
  have hy := Finset.sum_le_sum (s:=coupledDriftPairs N) (fun p hmem =>
    sqrt_weighted_young hK (hs _ (hp p hmem))
      (P p.1/(p.1 : ℝ)) (Q p.2 (p.1-p.2+1)))
  have he : (∑ p∈coupledDriftPairs N,
      2*Real.sqrt K*(P p.1/(p.1 : ℝ))*Q p.2 (p.1-p.2+1))=
      2*Real.sqrt K*(∑ d∈Finset.Icc 3 N,∑ a∈Finset.Icc 2 (d-1),
        (P d/(d : ℝ))*Q a (d-a+1)) := by
    rw [coupledDriftPairs,Finset.sum_sigma,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hf : (∑ p∈coupledDriftPairs N,s (p.1-p.2+1)*(P p.1/(p.1 : ℝ))^2)=
      ∑ d∈Finset.Icc 3 N,(∑ a∈Finset.Icc 2 (d-1),s (d-a+1))*
        (P d/(d : ℝ))^2 := by
    rw [coupledDriftPairs,Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.sum_mul]
  rw [he,Finset.sum_add_distrib,hf] at hy
  have hj := coupled_triangle_second_factor_weighted N P Q (fun b => K/s b)
    (fun b hb => div_nonneg hK (hs b hb).le) hjoint
  have hj' : (∑ p∈coupledDriftPairs N,
      (K/s (p.1-p.2+1))*(Q p.2 (p.1-p.2+1))^2)≤
      ∑ b∈Finset.Icc 2 N,(K*C/s b)*(P b)^2 := by
    convert hj using 1
    apply Finset.sum_congr rfl
    intro b hb
    ring
  exact hy.trans (add_le_add le_rfl hj')

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.coupled_triangle_weighted_young

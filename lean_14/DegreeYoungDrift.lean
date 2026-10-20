import ExactTriangleDriftYoung

/-! Degree-dependent Young weights in the actual triangular contraction sum. -/
noncomputable section
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def properYoungPrefix (s : ℕ→ℝ) (d : ℕ) : ℝ := ∑ b∈Finset.Icc 2 (d-1),s b

theorem coupled_triangle_weighted_first_factor (N : ℕ) (P s : ℕ→ℝ) :
    (∑ p∈coupledDriftPairs N,s (p.1-p.2+1)*(P p.1/(p.1 : ℝ))^2)=
      ∑ d∈Finset.Icc 3 N,properYoungPrefix s d*(P d/(d : ℝ))^2 := by
  classical
  rw [coupledDriftPairs,Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro d hd
  change (∑ a∈Finset.Icc 2 (d-1),s (d-a+1)*(P d/(d : ℝ))^2)=_
  rw [←Finset.sum_mul]
  unfold properYoungPrefix
  congr 1
  apply Finset.sum_bij (fun a _ => d-a+1)
  · intro a ha
    simp only [Finset.mem_Icc] at ha ⊢
    omega
  · intro a ha b hb he
    simp only [Finset.mem_Icc] at ha hb
    omega
  · intro b hb
    simp only [Finset.mem_Icc] at hb
    refine ⟨d-b+1,?_,?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · omega
  · intro a ha
    rfl

theorem coupled_triangle_weighted_second_factor
    (N : ℕ) (P : ℕ→ℝ) (Q : ℕ→ℕ→ℝ) (w : ℕ→ℝ)
    (hw : ∀ b,2≤b→0≤w b) {C : ℝ}
    (hjoint : ∀ b∈Finset.Icc 2 N,
      (∑ a∈Finset.Icc 2 (N-1),(Q a b)^2)≤C*(P b)^2) :
    (∑ p∈coupledDriftPairs N,w (p.1-p.2+1)*(Q p.2 (p.1-p.2+1))^2)≤
      ∑ b∈Finset.Icc 2 N,C*w b*(P b)^2 := by
  classical
  let e : (Σ _ : ℕ,ℕ)→ℕ×ℕ := fun p => (p.2,p.1-p.2+1)
  have hinj : Set.InjOn e (coupledDriftPairs N : Set (Σ _ : ℕ,ℕ)) := by
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
    _ = ∑ p∈(coupledDriftPairs N).image e,w p.2*(Q p.1 p.2)^2 :=
      (Finset.sum_image hinj).symm
    _ ≤ ∑ p∈(Finset.Icc 2 (N-1)).product (Finset.Icc 2 N),w p.2*(Q p.1 p.2)^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro p hp hn
        exact mul_nonneg (hw p.2 (Finset.mem_Icc.mp (Finset.mem_product.mp hp).2).1)
          (sq_nonneg _))
    _ = ∑ b∈Finset.Icc 2 N,∑ a∈Finset.Icc 2 (N-1),w b*(Q a b)^2 := by
      rw [Finset.product_eq_sprod,Finset.sum_product,Finset.sum_comm]
    _ ≤ ∑ b∈Finset.Icc 2 N,C*w b*(P b)^2 := by
      apply Finset.sum_le_sum
      intro b hb
      rw [←Finset.mul_sum]
      have hh := mul_le_mul_of_nonneg_left (hjoint b hb) (hw b (Finset.mem_Icc.mp hb).1)
      simpa only [mul_assoc,mul_comm,mul_left_comm] using hh

theorem coupled_triangle_degree_young
    (N : ℕ) (P : ℕ→ℝ) (Q : ℕ→ℕ→ℝ) (s : ℕ→ℝ)
    {C K : ℝ} (hK : 0≤K) (hs : ∀ b,2≤b→0<s b)
    (hjoint : ∀ b∈Finset.Icc 2 N,
      (∑ a∈Finset.Icc 2 (N-1),(Q a b)^2)≤C*(P b)^2) :
    2*Real.sqrt K*(∑ d∈Finset.Icc 3 N,∑ a∈Finset.Icc 2 (d-1),
      (P d/(d : ℝ))*Q a (d-a+1))≤
      (∑ d∈Finset.Icc 3 N,properYoungPrefix s d*(P d/(d : ℝ))^2)+
      (∑ b∈Finset.Icc 2 N,(K*C/s b)*(P b)^2) := by
  classical
  have hy := Finset.sum_le_sum (s:=coupledDriftPairs N) (fun p hp =>
    sqrt_weighted_young hK (hs (p.1-p.2+1) (by
      obtain ⟨hd,ha⟩ := Finset.mem_sigma.mp hp
      simp only [Finset.mem_Icc] at hd ha
      omega)) (P p.1/(p.1 : ℝ)) (Q p.2 (p.1-p.2+1)))
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
  rw [he,Finset.sum_add_distrib,coupled_triangle_weighted_first_factor] at hy
  have hj := coupled_triangle_weighted_second_factor N P Q (fun b => K/s b)
    (fun b hb => div_nonneg hK (hs b hb).le) hjoint
  have heq : (∑ b∈Finset.Icc 2 N,C*(K/s b)*(P b)^2)=
      ∑ b∈Finset.Icc 2 N,(K*C/s b)*(P b)^2 := by
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [heq] at hj
  exact hy.trans (add_le_add le_rfl hj)

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.coupled_triangle_degree_young

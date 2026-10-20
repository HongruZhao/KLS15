import SelectedRowsBoundaryTriangleYoung

/-! The unused canonical cell (2,N) is available in the full preceding
joint budget. Keeping it closes the finite last-cell refund exactly. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.ReservedQTriangleBudget
open KLS.DeterministicBridgeNext
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem coupled_triangle_second_factor_with_last_square
    (N : ℕ) (hN : 3 ≤ N) (P : ℕ → ℝ) (Q : ℕ → ℕ → ℝ) (v : ℕ → ℝ)
    {C : ℝ} (hv : ∀ b ∈ Finset.Icc 2 N,0 ≤ v b)
    (hjoint : ∀ b ∈ Finset.Icc 2 N,
      (∑ a ∈ Finset.Icc 2 (N-1),(Q a b)^2) ≤ C*(P b)^2) :
    (∑ p ∈ coupledDriftPairs N,v (p.1-p.2+1)*(Q p.2 (p.1-p.2+1))^2)+
      v N*(Q 2 N)^2 ≤ ∑ b ∈ Finset.Icc 2 N,v b*C*(P b)^2 := by
  classical
  let e : (Σ _ : ℕ,ℕ) → ℕ×ℕ:=fun p=>(p.2,p.1-p.2+1)
  have hinj:Set.InjOn e (coupledDriftPairs N : Set (Σ _ : ℕ,ℕ)) := by
    intro p hp q hq he
    have hp':=Finset.mem_sigma.mp hp
    have hq':=Finset.mem_sigma.mp hq
    have ha:=congrArg Prod.fst he
    have hb:=congrArg Prod.snd he
    simp only [e] at ha hb
    apply Sigma.ext
    · have hp2:=Finset.mem_Icc.mp hp'.2
      have hq2:=Finset.mem_Icc.mp hq'.2
      omega
    · simpa only [heq_eq_eq] using ha
  let rect:=(Finset.Icc 2 (N-1)).product (Finset.Icc 2 N)
  have hsub:(coupledDriftPairs N).image e ⊆ rect := by
    intro p hp
    obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp hp
    obtain ⟨hd,ha⟩:=Finset.mem_sigma.mp hq
    simp only [Finset.mem_Icc] at hd ha
    simp only [rect,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc,e]
    omega
  have htop:(2,N) ∈ rect := by
    simp only [rect,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc]
    omega
  have hnot:(2,N) ∉ (coupledDriftPairs N).image e := by
    intro hh
    obtain ⟨q,hq,he⟩:=Finset.mem_image.mp hh
    have hqa:=(Finset.mem_Icc.mp (Finset.mem_sigma.mp hq).1).2
    have hqb:=Finset.mem_Icc.mp (Finset.mem_sigma.mp hq).2
    have ha:=congrArg Prod.fst he
    have hb:=congrArg Prod.snd he
    simp only [e] at ha hb
    omega
  calc
    _=(∑ p ∈ (coupledDriftPairs N).image e,v p.2*(Q p.1 p.2)^2)+v N*(Q 2 N)^2 := by
      rw [Finset.sum_image hinj]
    _=∑ p ∈ insert (2,N) ((coupledDriftPairs N).image e),v p.2*(Q p.1 p.2)^2 := by
      rw [Finset.sum_insert hnot]
      ring
    _ ≤ ∑ p ∈ rect,v p.2*(Q p.1 p.2)^2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.insert_subset_iff.mpr ⟨htop,hsub⟩)
      intro p hp _
      exact mul_nonneg (hv p.2 (Finset.mem_product.mp hp).2) (sq_nonneg _)
    _=∑ b ∈ Finset.Icc 2 N,v b*(∑ a ∈ Finset.Icc 2 (N-1),(Q a b)^2) := by
      dsimp only [rect]
      rw [Finset.product_eq_sprod,Finset.sum_product,Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]
    _ ≤ _:=Finset.sum_le_sum fun b hb=>by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hjoint b hb) (hv b hb)


theorem coupled_triangle_selected_rows_young_with_last_refund (N : ℕ) (hN : 3 ≤ N) (P : ℕ → ℝ)
    (Q : ℕ → ℕ → ℝ) (s : ℕ → ℝ) (rho lambda : ℕ → ℕ → ℝ) {C K : ℝ}
    (hK : 0 ≤ K) (hs : ∀ b, 2 ≤ b → 0 < s b)
    (hlambda : ∀ a b, 2 ≤ a → 2 ≤ b → lambda a b ≤ 1)
    (hboundary : ∀ d a, 3 ≤ d → a ∈ Finset.Icc 2 (d-1) →
      lambda a (d-a+1) = 1 → rho d a = 0)
    (hjoint : ∀ b ∈ Finset.Icc 2 N,
      (∑ a ∈ Finset.Icc 2 (N-1), (Q a b)^2) ≤ C*(P b)^2) :
    2*Real.sqrt K*(∑ d ∈ Finset.Icc 3 N, ∑ a ∈ Finset.Icc 2 (d-1),
      rho d a*(P d/(d : ℝ))*Q a (d-a+1)) +
      (∑ p ∈ coupledDriftPairs N,
        (lambda p.2 (p.1-p.2+1)*K/s (p.1-p.2+1))*(Q p.2 (p.1-p.2+1))^2) +
      (lambda 2 N*K/s N)*(Q 2 N)^2 ≤
      (∑ d ∈ Finset.Icc 3 N, selectedRowsPrefix s rho lambda d*(P d/(d : ℝ))^2) +
      ∑ b ∈ Finset.Icc 2 N, (K*C/s b)*(P b)^2 := by
  classical
  have hp : ∀ p ∈ coupledDriftPairs N, 2 ≤ p.2 ∧ 2 ≤ p.1-p.2+1 := by
    intro p hp
    obtain ⟨hd,ha⟩ := Finset.mem_sigma.mp hp
    simp only [Finset.mem_Icc] at hd ha
    omega
  have hy := Finset.sum_le_sum (s := coupledDriftPairs N) (fun p hmem => show
      2*Real.sqrt K*(rho p.1 p.2*(P p.1/(p.1 : ℝ)))*Q p.2 (p.1-p.2+1) ≤
      (s (p.1-p.2+1)/(1-lambda p.2 (p.1-p.2+1)))*
        (rho p.1 p.2*(P p.1/(p.1 : ℝ)))^2+
      (K/(s (p.1-p.2+1)/(1-lambda p.2 (p.1-p.2+1))))*
        (Q p.2 (p.1-p.2+1))^2 from by
    by_cases heq : lambda p.2 (p.1-p.2+1) = 1
    · have hmem' := Finset.mem_sigma.mp hmem
      have hr := hboundary p.1 p.2 (Finset.mem_Icc.mp hmem'.1).1 hmem'.2 heq
      simp [heq,hr]
    · have hpos : 0 < 1-lambda p.2 (p.1-p.2+1) := by
        have hh := hlambda p.2 (p.1-p.2+1) (hp p hmem).1 (hp p hmem).2
        exact sub_pos.mpr (lt_of_le_of_ne hh heq)
      exact sqrt_weighted_young hK (div_pos (hs _ (hp p hmem).2) hpos)
        (rho p.1 p.2*(P p.1/(p.1 : ℝ))) (Q p.2 (p.1-p.2+1)))
  have he : (∑ p ∈ coupledDriftPairs N, 2*Real.sqrt K *
      (rho p.1 p.2*(P p.1/(p.1 : ℝ)))*Q p.2 (p.1-p.2+1)) =
      2*Real.sqrt K*(∑ d ∈ Finset.Icc 3 N, ∑ a ∈ Finset.Icc 2 (d-1),
        rho d a*(P d/(d : ℝ))*Q a (d-a+1)) := by
    rw [coupledDriftPairs,Finset.sum_sigma,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hfirst : (∑ p ∈ coupledDriftPairs N,
      (s (p.1-p.2+1)/(1-lambda p.2 (p.1-p.2+1))) *
        (rho p.1 p.2*(P p.1/(p.1 : ℝ)))^2) =
      ∑ d ∈ Finset.Icc 3 N, selectedRowsPrefix s rho lambda d*(P d/(d : ℝ))^2 := by
    rw [coupledDriftPairs,Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro d hd
    unfold selectedRowsPrefix
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hsecond : (∑ p ∈ coupledDriftPairs N,
      (K/(s (p.1-p.2+1)/(1-lambda p.2 (p.1-p.2+1)))) *
        (Q p.2 (p.1-p.2+1))^2) =
      (∑ p ∈ coupledDriftPairs N, (K/s (p.1-p.2+1)) *
        (Q p.2 (p.1-p.2+1))^2) -
      ∑ p ∈ coupledDriftPairs N,
        (lambda p.2 (p.1-p.2+1)*K/s (p.1-p.2+1))*(Q p.2 (p.1-p.2+1))^2 := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hmem
    rw [div_div_eq_mul_div]
    ring
  rw [he,Finset.sum_add_distrib,hfirst,hsecond] at hy
  have hNmem : N ∈ Finset.Icc 2 N := by simp only [Finset.mem_Icc]; omega
  have hj := coupled_triangle_second_factor_with_last_square N hN P Q (fun b=>K/s b)
    (fun b hb=>div_nonneg hK (hs b (Finset.mem_Icc.mp hb).1).le) hjoint
  have htop : (lambda 2 N*K/s N)*(Q 2 N)^2 ≤ (K/s N)*(Q 2 N)^2 := by
    have hc := mul_le_mul_of_nonneg_right (hlambda 2 N (by omega) (by omega))
      (mul_nonneg (div_nonneg hK (hs N (by omega)).le) (sq_nonneg (Q 2 N)))
    convert hc using 1 <;> ring
  have hj' : (∑ p ∈ coupledDriftPairs N, (K/s (p.1-p.2+1)) *
      (Q p.2 (p.1-p.2+1))^2)+(K/s N)*(Q 2 N)^2 ≤
      ∑ b ∈ Finset.Icc 2 N, (K*C/s b)*(P b)^2 := by
    convert hj using 1
    apply Finset.sum_congr rfl
    intro b hb
    ring
  linarith

end KLSConstantImprovement.ReservedQTriangleBudget
#print axioms KLSConstantImprovement.ReservedQTriangleBudget.coupled_triangle_second_factor_with_last_square

#print axioms KLSConstantImprovement.ReservedQTriangleBudget.coupled_triangle_selected_rows_young_with_last_refund

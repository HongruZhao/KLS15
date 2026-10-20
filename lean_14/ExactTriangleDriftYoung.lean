import CoupledDriftCauchy

/-! Exact triangular Young control before replacing (d-2)/d² by1/8.
The joint cumulant square sum is retained without individualizing its norms. -/
noncomputable section
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem coupled_triangle_first_factor_exact (N : ℕ) (P : ℕ → ℝ) :
    (∑ p∈coupledDriftPairs N,(P p.1/(p.1 : ℝ))^2) =
      ∑ d∈Finset.Icc 3 N,((d : ℝ)-2)*(P d/(d : ℝ))^2 := by
  classical
  rw [coupledDriftPairs,Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro d hd
  have hd3 := (Finset.mem_Icc.mp hd).1
  have hc : (Finset.Icc 2 (d-1)).card=d-2 := by
    simp only [Nat.card_Icc]
    omega
  change (∑ _a∈Finset.Icc 2 (d-1),(P d/(d : ℝ))^2)=_
  rw [Finset.sum_const,hc,nsmul_eq_mul]
  have hcast : ((d-2 : ℕ) : ℝ)=(d : ℝ)-2 := by
    rw [Nat.cast_sub (by omega : 2≤d)]
    norm_num
  rw [hcast]

theorem sqrt_weighted_young {K s : ℝ} (hK : 0≤K) (hs : 0<s) (x y : ℝ) :
    2*Real.sqrt K*x*y ≤ s*x^2+(K/s)*y^2 := by
  apply (mul_le_mul_iff_of_pos_right hs).mp
  have he : (s*x^2+(K/s)*y^2)*s=s^2*x^2+K*y^2 := by
    field_simp
  rw [he]
  have hsq := sq_nonneg (s*x-Real.sqrt K*y)
  have hKsq := Real.sq_sqrt hK
  have heq : (s*x-Real.sqrt K*y)^2=s^2*x^2-2*s*Real.sqrt K*x*y+K*y^2 := by
    calc
      _ = s^2*x^2-2*s*Real.sqrt K*x*y+(Real.sqrt K)^2*y^2 := by ring
      _ = _ := by rw [hKsq]
  rw [heq] at hsq
  nlinarith

theorem coupled_triangle_young (N : ℕ) (P : ℕ → ℝ) (Q : ℕ → ℕ → ℝ)
    {C K s : ℝ} (_hC : 0≤C) (hK : 0≤K) (hs : 0<s)
    (hjoint : ∀ b∈Finset.Icc 2 N,
      (∑ a∈Finset.Icc 2 (N-1),(Q a b)^2) ≤ C*(P b)^2) :
    2*Real.sqrt K*(∑ d∈Finset.Icc 3 N,∑ a∈Finset.Icc 2 (d-1),
      (P d/(d : ℝ))*Q a (d-a+1)) ≤
      s*(∑ d∈Finset.Icc 3 N,((d : ℝ)-2)*(P d/(d : ℝ))^2)+
      (K*C/s)*(∑ d∈Finset.Icc 2 N,(P d)^2) := by
  classical
  have hy := Finset.sum_le_sum (s:=coupledDriftPairs N) (fun p hp =>
    sqrt_weighted_young hK hs (P p.1/(p.1 : ℝ)) (Q p.2 (p.1-p.2+1)))
  have he : (∑ p∈coupledDriftPairs N,
      2*Real.sqrt K*(P p.1/(p.1 : ℝ))*Q p.2 (p.1-p.2+1)) =
      2*Real.sqrt K*(∑ d∈Finset.Icc 3 N,∑ a∈Finset.Icc 2 (d-1),
        (P d/(d : ℝ))*Q a (d-a+1)) := by
    rw [coupledDriftPairs,Finset.sum_sigma,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [he,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,
    coupled_triangle_first_factor_exact] at hy
  have hj := coupled_triangle_second_factor N P Q hjoint
  have hm := mul_le_mul_of_nonneg_left hj (div_nonneg hK hs.le)
  calc
    _ ≤ _ := hy
    _ ≤ s*(∑ d∈Finset.Icc 3 N,((d : ℝ)-2)*(P d/(d : ℝ))^2)+
        (K/s)*(C*(∑ d∈Finset.Icc 2 N,(P d)^2)) := add_le_add le_rfl hm
    _ = _ := by ring

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.coupled_triangle_young

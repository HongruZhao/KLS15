import Mathlib

/-! The finite triangular Cauchy estimate used for coupled Appell drift.
The joint square-sum hypothesis is kept intact; no sum of individual
operator norms is introduced. -/
noncomputable section
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def coupledDriftPairs (N : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.Icc 3 N).sigma (fun d => Finset.Icc 2 (d-1))

theorem coupled_triangle_first_factor (N : ℕ) (P : ℕ → ℝ) :
    (∑ p ∈ coupledDriftPairs N, (P p.1/(p.1 : ℝ))^2) ≤
      (1/8 : ℝ)*(∑ d ∈ Finset.Icc 2 N, (P d)^2) := by
  classical
  rw [coupledDriftPairs, Finset.sum_sigma]
  have hper (d : ℕ) (hd : d ∈ Finset.Icc 3 N) :
      (∑ _a ∈ Finset.Icc 2 (d-1), (P d/(d : ℝ))^2) ≤ (1/8 : ℝ)*(P d)^2 := by
    have hd3 := (Finset.mem_Icc.mp hd).1
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hc : (Finset.Icc 2 (d-1)).card = d-2 := by
      simp only [Nat.card_Icc]
      omega
    rw [Finset.sum_const, hc, nsmul_eq_mul]
    have hcast : ((d-2 : ℕ) : ℝ) = (d : ℝ)-2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ d)]
      norm_num
    rw [hcast, div_pow]
    have hp : 8*((d : ℝ)-2) ≤ (d : ℝ)^2 := by nlinarith [sq_nonneg ((d : ℝ)-4)]
    have hh := mul_le_mul_of_nonneg_right hp (sq_nonneg (P d))
    have hds : (0 : ℝ) < (d : ℝ)^2 := sq_pos_of_pos hd0
    calc
      _ = (((d : ℝ)-2)*(P d)^2)/(d : ℝ)^2 := by ring
      _ ≤ (P d)^2/8 := (div_le_div_iff₀ hds (by norm_num : (0 : ℝ) < 8)).mpr (by nlinarith)
      _ = _ := by ring
  calc
    _ ≤ ∑ d ∈ Finset.Icc 3 N, (1/8 : ℝ)*(P d)^2 := Finset.sum_le_sum hper
    _ = (1/8 : ℝ)*(∑ d ∈ Finset.Icc 3 N, (P d)^2) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg (by intro d hd; simp only [Finset.mem_Icc] at hd ⊢; omega)
        (by intro d hd hn; exact sq_nonneg _)) (by norm_num)

theorem coupled_triangle_second_factor (N : ℕ) (P : ℕ → ℝ) (Q : ℕ → ℕ → ℝ)
    {C : ℝ} (hjoint : ∀ b ∈ Finset.Icc 2 N,
      (∑ a ∈ Finset.Icc 2 (N-1), (Q a b)^2) ≤ C*(P b)^2) :
    (∑ p ∈ coupledDriftPairs N, (Q p.2 (p.1-p.2+1))^2) ≤
      C*(∑ b ∈ Finset.Icc 2 N, (P b)^2) := by
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
    simp only [e, Finset.mem_product, Finset.mem_Icc]
    omega
  calc
    _ = ∑ p ∈ (coupledDriftPairs N).image e, (Q p.1 p.2)^2 :=
      (Finset.sum_image hinj).symm
    _ ≤ ∑ p ∈ (Finset.Icc 2 (N-1)).product (Finset.Icc 2 N), (Q p.1 p.2)^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro p hp hn; exact sq_nonneg _)
    _ = ∑ b ∈ Finset.Icc 2 N, ∑ a ∈ Finset.Icc 2 (N-1), (Q a b)^2 := by
      rw [Finset.product_eq_sprod, Finset.sum_product, Finset.sum_comm]
    _ ≤ ∑ b ∈ Finset.Icc 2 N, C*(P b)^2 := Finset.sum_le_sum hjoint
    _ = _ := (Finset.mul_sum ..).symm

theorem coupled_triangle_cauchy_sq (N : ℕ) (P : ℕ → ℝ) (Q : ℕ → ℕ → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hjoint : ∀ b ∈ Finset.Icc 2 N,
      (∑ a ∈ Finset.Icc 2 (N-1), (Q a b)^2) ≤ C*(P b)^2) :
    (∑ d ∈ Finset.Icc 3 N, ∑ a ∈ Finset.Icc 2 (d-1),
      (P d/(d : ℝ))*Q a (d-a+1))^2 ≤
      C/8*(∑ d ∈ Finset.Icc 2 N, (P d)^2)^2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (coupledDriftPairs N)
    (fun p => P p.1/(p.1 : ℝ)) (fun p => Q p.2 (p.1-p.2+1))
  have hf := coupled_triangle_first_factor N P
  have hg := coupled_triangle_second_factor N P Q hjoint
  have hmul := mul_le_mul hf hg (Finset.sum_nonneg (by intro p hp; exact sq_nonneg _))
    (by positivity : 0 ≤ (1/8 : ℝ)*(∑ d ∈ Finset.Icc 2 N, (P d)^2))
  have hh := hcs.trans hmul
  simpa only [coupledDriftPairs, Finset.sum_sigma] using (show _ from hh)
    |>.trans_eq (by ring)

theorem coupled_triangle_cauchy (N : ℕ) (P : ℕ → ℝ) (Q : ℕ → ℕ → ℝ)
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (hjoint : ∀ b ∈ Finset.Icc 2 N,
      (∑ a ∈ Finset.Icc 2 (N-1), (Q a b)^2) ≤ C*(P b)^2) :
    2*Real.sqrt K*(∑ d ∈ Finset.Icc 3 N, ∑ a ∈ Finset.Icc 2 (d-1),
      (P d/(d : ℝ))*Q a (d-a+1)) ≤
      Real.sqrt (K*C/2)*(∑ d ∈ Finset.Icc 2 N, (P d)^2) := by
  have hh := coupled_triangle_cauchy_sq N P Q hC hjoint
  have hKsq := Real.sq_sqrt hK
  have hRsq := Real.sq_sqrt (by positivity : 0 ≤ K*C/2)
  have hD : 0 ≤ ∑ d ∈ Finset.Icc 2 N, (P d)^2 := Finset.sum_nonneg (by intro d hd; positivity)
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 4*K by positivity)
  have hright : 0 ≤ Real.sqrt (K*C/2)*(∑ d ∈ Finset.Icc 2 N, (P d)^2) := by positivity
  nlinarith

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.coupled_triangle_cauchy

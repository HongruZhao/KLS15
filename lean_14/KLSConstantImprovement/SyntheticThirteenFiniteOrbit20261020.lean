import KLSConstantImprovement.WeightedOrbitBellmanTail

/-! A small rational finite-payment scalar orbit with raw initialenergy12.
For14571/1250<=K<=12, its normalized initialratio is12/K. Seven actual
payments are dominated by the displayed synthetic observationsz2..z8.
The normalized orbit is positive and constant fromindex8, hence has every
subexponential envelope. It satisfies the weak original scalar recurrence.
This is NOT an admissible-law extremizer or a proved syntheticbudgetbridge.
Root alone compiles this draft. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.SyntheticThirteenFiniteOrbit20261020
open KLSConstantImprovement.WeightedOrbitBellmanTail
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

def y (i : ℕ) : ℝ :=
  if i=0 then 1 else
  if i=1 then 12 else
  if i=2 then 142 else
  if i=3 then 8352/5 else
  if i=4 then 97917/5 else
  if i=5 then 229088 else
  if i=6 then 13378599/5 else
  if i=7 then 156078374/5 else
  3638394929/10

def z (d : ℕ) : ℝ :=
  if d=2 then 2 else
  if d=3 then 10 else
  if d=4 then 265/4 else
  if d=5 then 1007/2 else
  if d=6 then 150043/36 else
  if d=7 then 16054601/441 else
  if d=8 then 1557296297/4704 else
  0

def Z (K : ℝ) (i : ℕ) : ℝ :=
  if i ≤ 8 then y i/K^i else y 8/K^8

def c (K : ℝ) (i : ℕ) : ℝ :=
  if i < 7 then z (i+2)/K^(i+2) else 0

def syntheticSpend (K : ℝ) (w : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range 7,w i*(z (i+2)/K^(i+2))

theorem y_positive (i : ℕ) : 0 < y i := by
  unfold y
  split_ifs <;> norm_num

theorem y_le_last (i : ℕ) : y i ≤ y 8 := by
  have he : y 8=(3638394929/10 : ℝ) := by norm_num [y]
  rw [he]
  unfold y
  split_ifs <;> norm_num

theorem z_nonnegative (d : ℕ) : 0 ≤ z d := by
  unfold z
  split_ifs <;> norm_num

theorem raw_recurrence (i : ℕ) (hi : i < 7) :
    (y (i+1))^2/y i-z (i+2) ≤ y (i+2) := by
  interval_cases i <;> norm_num [y,z]

theorem raw_cap (i : ℕ) (hi : i < 7) : z (i+2) ≤ 2*y i := by
  interval_cases i <;> norm_num [y,z]

theorem raw_upper (i : ℕ) (hi : i < 8) : y (i+1) ≤ 12*y i := by
  interval_cases i <;> norm_num [y]

theorem last_ratio_bound : y 8 ≤ (14571/1250 : ℝ)*y 7 := by
  norm_num [y]

theorem K_positive {K : ℝ} (hK : (14571/1250 : ℝ) ≤ K) : 0 < K := by
  linarith

theorem Z_prefix (K : ℝ) (i : ℕ) (hi : i ≤ 8) : Z K i=y i/K^i := by
  simp only [Z,if_pos hi]

theorem Z_tail (K : ℝ) (i : ℕ) (hi : 8 ≤ i) : Z K i=y 8/K^8 := by
  by_cases he : i ≤ 8
  · have heq : i=8 := by omega
    subst i
    simp only [Z,le_refl,if_true]
  · simp only [Z,if_neg he]

theorem c_tail (K : ℝ) (i : ℕ) (hi : 7 ≤ i) : c K i=0 := by
  simp only [c,if_neg (show ¬i < 7 by omega)]

theorem Z_positive (K : ℝ) (hK : 0 < K) (i : ℕ) : 0 < Z K i := by
  by_cases hi : i ≤ 8
  · rw [Z_prefix K i hi]
    exact div_pos (y_positive i) (pow_pos hK i)
  · rw [Z_tail K i (by omega)]
    exact div_pos (y_positive 8) (pow_pos hK 8)

theorem c_nonnegative (K : ℝ) (hK : 0 < K) (i : ℕ) : 0 ≤ c K i := by
  by_cases hi : i < 7
  · rw [c,if_pos hi]
    exact div_nonneg (z_nonnegative _) (pow_nonneg hK.le _)
  · simp only [c,if_neg hi,le_refl]

theorem normalized_recurrence_identity (K x0 x1 u : ℝ) (i : ℕ)
    (hK : K≠0) (hx0 : x0≠0) :
    (x1/K^(i+1))^2/(x0/K^i)-u/K^(i+2)=
      (x1^2/x0-u)/K^(i+2) := by
  simp only [pow_add,pow_one]
  field_simp [hK,hx0,pow_ne_zero i hK] <;> ring

theorem last_step_nonincrease (K : ℝ) (hK : (14571/1250 : ℝ) ≤ K) :
    Z K 8 ≤ Z K 7 := by
  have hK0 : 0 < K := K_positive hK
  have hraw : y 8 ≤ K*y 7 :=
    last_ratio_bound.trans (mul_le_mul_of_nonneg_right hK (y_positive 7).le)
  rw [Z_prefix K 8 (by omega),Z_prefix K 7 (by omega)]
  apply (div_le_iff₀ (pow_pos hK0 8)).mpr
  calc
    y 8 ≤ K*y 7 := hraw
    _ = (y 7/K^7)*K^8 := by
      rw [show K^8=K^7*K from pow_succ K 7]
      field_simp [ne_of_gt hK0,pow_ne_zero 7 (ne_of_gt hK0)] <;> ring

theorem normalized_recurrence (K : ℝ) (hK : (14571/1250 : ℝ) ≤ K)
    (i : ℕ) : (Z K (i+1))^2/Z K i-c K i ≤ Z K (i+2) := by
  have hK0 : 0 < K := K_positive hK
  by_cases hi : i < 7
  · rw [Z_prefix K i (by omega),Z_prefix K (i+1) (by omega),
      Z_prefix K (i+2) (by omega),c,if_pos hi,
      normalized_recurrence_identity K (y i) (y (i+1)) (z (i+2)) i
        (ne_of_gt hK0) (ne_of_gt (y_positive i))]
    exact div_le_div_of_nonneg_right (raw_recurrence i hi) (pow_nonneg hK0.le _)
  · by_cases hi7 : i=7
    · subst i
      have hh : (Z K 8)^2/Z K 7 ≤ Z K 8 := by
        apply (div_le_iff₀ (Z_positive K hK0 7)).mpr
        simpa only [pow_two] using
          mul_le_mul_of_nonneg_left (last_step_nonincrease K hK) (Z_positive K hK0 8).le
      simpa only [c_tail K 7 (by omega),sub_zero,
        Z_tail K 9 (by omega),Z_tail K 8 (by omega)] using hh
    · have hi8 : 8 ≤ i := by omega
      rw [Z_tail K i hi8,Z_tail K (i+1) (by omega),
        Z_tail K (i+2) (by omega),c_tail K i (by omega),sub_zero]
      have hv : y 8/K^8≠0 := ne_of_gt (div_pos (y_positive 8) (pow_pos hK0 8))
      have he : (y 8/K^8)^2/(y 8/K^8)=y 8/K^8 := by
        field_simp [hv] <;> ring
      exact he.le

theorem normalized_cap (K : ℝ) (hK : 0 < K) (i : ℕ) :
    c K i ≤ (2/K^2)*Z K i := by
  by_cases hi : i < 7
  · rw [c,if_pos hi,Z_prefix K i (by omega)]
    have he : (2/K^2)*(y i/K^i)=(2*y i)/K^(i+2) := by
      simp only [pow_add]
      field_simp [ne_of_gt hK,pow_ne_zero i (ne_of_gt hK)] <;> ring
    rw [he]
    exact div_le_div_of_nonneg_right (raw_cap i hi) (pow_nonneg hK.le _)
  · rw [c,if_neg hi]
    exact mul_nonneg (by positivity) (Z_positive K hK i).le

theorem normalized_upper (K : ℝ) (hK : (14571/1250 : ℝ) ≤ K)
    (hK12 : K ≤ 12) (i : ℕ) : Z K (i+1) ≤ (12/K)*Z K i := by
  have hK0 : 0 < K := K_positive hK
  by_cases hi : i < 8
  · rw [Z_prefix K i (by omega),Z_prefix K (i+1) (by omega)]
    have he : (12/K)*(y i/K^i)=(12*y i)/K^(i+1) := by
      simp only [pow_add,pow_one]
      field_simp [ne_of_gt hK0,pow_ne_zero i (ne_of_gt hK0)] <;> ring
    rw [he]
    exact div_le_div_of_nonneg_right (raw_upper i hi) (pow_nonneg hK0.le _)
  · rw [Z_tail K i (by omega),Z_tail K (i+1) (by omega)]
    have hp : 1 ≤ 12/K := (le_div_iff₀ hK0).mpr (by linarith)
    simpa only [mul_comm] using
      le_mul_of_one_le_right (div_pos (y_positive 8) (pow_pos hK0 8)).le hp

theorem Z_bounded (K : ℝ) (hK : (14571/1250 : ℝ) ≤ K) (i : ℕ) :
    Z K i ≤ y 8 := by
  have hK1 : 1 ≤ K := by linarith
  by_cases hi : i ≤ 8
  · rw [Z_prefix K i hi]
    exact (div_le_self (y_positive i).le (one_le_pow₀ hK1)).trans (y_le_last i)
  · rw [Z_tail K i (by omega)]
    exact div_le_self (y_positive 8).le (one_le_pow₀ hK1)

theorem all_rate_envelope (K : ℝ) (hK : (14571/1250 : ℝ) ≤ K) :
    ∀ ρ : ℝ,1 < ρ → ∃ M : ℝ,∀ i : ℕ,Z K i ≤ M*ρ^i := by
  intro ρ hρ
  refine ⟨y 8,fun i=>?_⟩
  exact (Z_bounded K hK i).trans
    (le_mul_of_one_le_right (y_positive 8).le (one_le_pow₀ hρ.le))

theorem spend_le_synthetic (K : ℝ) (hK : 0 < K) (w : ℕ → ℝ)
    (hw : ∀ i : ℕ,0 ≤ w i) (N : ℕ) :
    spend w (c K) N ≤ syntheticSpend K w := by
  have hnonneg (i : ℕ) : 0 ≤ w i*c K i := mul_nonneg (hw i) (c_nonnegative K hK i)
  have he : (∑ i ∈ Finset.range N ∩ Finset.range 7,w i*c K i)=
      (∑ i ∈ Finset.range N,w i*c K i) := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro i hi hnot
    have hi7 : 7 ≤ i := by
      by_contra hfail
      exact hnot (Finset.mem_inter.mpr ⟨hi,Finset.mem_range.mpr (by omega)⟩)
    rw [c_tail K i hi7,mul_zero]
  have hle : (∑ i ∈ Finset.range N,w i*c K i) ≤
      (∑ i ∈ Finset.range 7,w i*c K i) := by
    rw [←he]
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    intro i _ _
    exact hnonneg i
  unfold spend
  calc
    _ ≤ ∑ i ∈ Finset.range 7,w i*c K i := hle
    _ = syntheticSpend K w := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [syntheticSpend,c,if_pos (Finset.mem_range.mp hi)]

theorem sum_Icc_two_eight (f : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 2 8,f d)=∑ i ∈ Finset.range 7,f (i+2) := by
  classical
  apply Finset.sum_bij (fun d _=>d-2)
  · intro d hd
    simp only [Finset.mem_Icc,Finset.mem_range] at hd ⊢
    omega
  · intro a ha b hb hab
    simp only [Finset.mem_Icc] at ha hb
    omega
  · intro i hi
    refine ⟨i+2,?_,by omega⟩
    simp only [Finset.mem_Icc,Finset.mem_range] at hi ⊢
    omega
  · intro d hd
    have he : d-2+2=d := by
      have hd2 := (Finset.mem_Icc.mp hd).1
      omega
    rw [he]

theorem syntheticSpend_eq_Icc (K : ℝ) (t : ℕ → ℝ) :
    syntheticSpend K (fun i=>t (i+2))=
      ∑ d ∈ Finset.Icc 2 8,t d*z d/K^d := by
  rw [sum_Icc_two_eight]
  unfold syntheticSpend
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The analytic synthetic-budget bridge is an explicit premise here. -/
theorem spend_le_budget (K C : ℝ) (hK : 0 < K) (t : ℕ → ℝ)
    (ht : ∀ d : ℕ,2 ≤ d → 0 ≤ t d)
    (hbridge : (∑ d ∈ Finset.Icc 2 8,t d*z d/K^d) ≤ C) (N : ℕ) :
    spend (fun i=>t (i+2)) (c K) N ≤ C := by
  calc
    _ ≤ syntheticSpend K (fun i=>t (i+2)) :=
      spend_le_synthetic K hK (fun i=>t (i+2)) (fun i=>ht (i+2) (by omega)) N
    _ = _ := syntheticSpend_eq_Icc K t
    _ ≤ C := hbridge

/-- The uniform finite-payment witness, conditional only on a scalar
syntheticbudget bound when that bound is later supplied. -/
theorem uniform_scalar_orbit (K : ℝ) (hK : (14571/1250 : ℝ) ≤ K)
    (hK12 : K ≤ 12) :
    Z K 0=1 ∧ Z K 1=12/K ∧ (∀ i : ℕ,0 < Z K i) ∧
      (∀ i : ℕ,0 ≤ c K i) ∧
      (∀ i : ℕ,(Z K (i+1))^2/Z K i-c K i ≤ Z K (i+2)) ∧
      (∀ i : ℕ,c K i ≤ (2/K^2)*Z K i) ∧
      (∀ i : ℕ,Z K (i+1) ≤ (12/K)*Z K i) ∧
      (∀ ρ : ℝ,1 < ρ → ∃ M : ℝ,∀ i : ℕ,Z K i ≤ M*ρ^i) := by
  exact ⟨by norm_num [Z,y],by norm_num [Z,y],
    Z_positive K (K_positive hK),c_nonnegative K (K_positive hK),
    normalized_recurrence K hK,normalized_cap K (K_positive hK),
    normalized_upper K hK hK12,all_rate_envelope K hK⟩

end KLSConstantImprovement.SyntheticThirteenFiniteOrbit20261020
#print axioms KLSConstantImprovement.SyntheticThirteenFiniteOrbit20261020.raw_recurrence
#print axioms KLSConstantImprovement.SyntheticThirteenFiniteOrbit20261020.normalized_recurrence
#print axioms KLSConstantImprovement.SyntheticThirteenFiniteOrbit20261020.normalized_cap
#print axioms KLSConstantImprovement.SyntheticThirteenFiniteOrbit20261020.spend_le_synthetic
#print axioms KLSConstantImprovement.SyntheticThirteenFiniteOrbit20261020.spend_le_budget
#print axioms KLSConstantImprovement.SyntheticThirteenFiniteOrbit20261020.uniform_scalar_orbit

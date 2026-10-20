import KLSConstantImprovement.ActualProperInfiniteValuePayment

/-! Contract the positive part of a normalized scalar orbit while keeping
Z₀ = 1.  The initial recurrence becomes easier; every later recurrence
is homogeneous.  This isolated draft has not been compiled by its author. -/

noncomputable section
namespace KLSConstantImprovement.NormalizedScalarInitialContraction
open KLSConstantImprovement.WeightedOrbitBellmanTail

def contractedZ (k : ℝ) (Z : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => k * Z (n + 1)

def contractedC (k : ℝ) (c : ℕ → ℝ) (n : ℕ) : ℝ := k * c n

@[simp] theorem contractedZ_zero (k : ℝ) (Z : ℕ → ℝ) : contractedZ k Z 0 = 1 := rfl
@[simp] theorem contractedZ_one (k : ℝ) (Z : ℕ → ℝ) : contractedZ k Z 1 = k * Z 1 := rfl

theorem contractedZ_nonneg {k : ℝ} (hk : 0 ≤ k) {Z : ℕ → ℝ}
    (hZ : ∀ i : ℕ, 0 ≤ Z i) (i : ℕ) : 0 ≤ contractedZ k Z i := by
  cases i with
  | zero => exact zero_le_one
  | succ i => exact mul_nonneg hk (hZ _)

theorem contractedC_nonneg {k : ℝ} (hk : 0 ≤ k) {c : ℕ → ℝ}
    (hc : ∀ i : ℕ, 0 ≤ c i) (i : ℕ) : 0 ≤ contractedC k c i := mul_nonneg hk (hc i)

theorem contracted_recurrence {k : ℝ} (hk : 0 < k) (hk1 : k ≤ 1)
    {Z c : ℕ → ℝ} (hZ0 : Z 0 = 1)
    (hrec : ∀ i : ℕ, 0 < Z i → 0 < Z (i + 1) →
      Z (i + 1) ^ 2 / Z i - c i ≤ Z (i + 2))
    (i : ℕ) (hi : 0 < contractedZ k Z i) (hi1 : 0 < contractedZ k Z (i + 1)) :
    contractedZ k Z (i + 1) ^ 2 / contractedZ k Z i - contractedC k c i ≤
      contractedZ k Z (i + 2) := by
  cases i with
  | zero =>
    have hz1 : 0 < Z 1 := (mul_pos_iff_of_pos_left hk).mp hi1
    have hh := hrec 0 (by simpa only [hZ0] using zero_lt_one) hz1
    rw [hZ0, div_one] at hh
    have hm := mul_le_mul_of_nonneg_left hh hk.le
    have hkk : k ^ 2 ≤ k := by nlinarith [mul_nonneg hk.le (sub_nonneg.mpr hk1)]
    have hs := mul_le_mul_of_nonneg_right hkk (sq_nonneg (Z 1))
    change (k * Z 1) ^ 2 / 1 - k * c 0 ≤ k * Z 2
    rw [div_one]
    nlinarith only [hm, hs]
  | succ i =>
    have hzi : 0 < Z (i + 1) := (mul_pos_iff_of_pos_left hk).mp hi
    have hzi1 : 0 < Z (i + 2) := (mul_pos_iff_of_pos_left hk).mp hi1
    have hh := mul_le_mul_of_nonneg_left (hrec (i + 1) hzi hzi1) hk.le
    change (k * Z (i + 2)) ^ 2 / (k * Z (i + 1)) - k * c (i + 1) ≤ k * Z (i + 3)
    have he : (k * Z (i + 2)) ^ 2 / (k * Z (i + 1)) - k * c (i + 1) =
        k * (Z (i + 2) ^ 2 / Z (i + 1) - c (i + 1)) := by
      field_simp [ne_of_gt hk, ne_of_gt hzi] <;> ring
    rw [he]
    exact hh

theorem contracted_cap {k A : ℝ} (hk : 0 ≤ k) (hk1 : k ≤ 1) (hA : 0 ≤ A)
    {Z c : ℕ → ℝ} (hZ0 : Z 0 = 1) (hcap : ∀ i : ℕ, c i ≤ A * Z i) (i : ℕ) :
    contractedC k c i ≤ A * contractedZ k Z i := by
  cases i with
  | zero =>
    have hh := mul_le_mul_of_nonneg_left (hcap 0) hk
    have ha := mul_le_mul_of_nonneg_right hk1 hA
    simp only [hZ0, mul_one] at hh
    change k * c 0 ≤ A * 1
    nlinarith only [hh, ha]
  | succ i =>
    have hh := mul_le_mul_of_nonneg_left (hcap (i + 1)) hk
    change k * c (i + 1) ≤ A * (k * Z (i + 1))
    nlinarith only [hh]

theorem contracted_spend (k : ℝ) (w c : ℕ → ℝ) (N : ℕ) :
    spend w (contractedC k c) N = k * spend w c N := by
  unfold spend contractedC
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem contracted_envelope {k : ℝ} (hk : 0 ≤ k) (hk1 : k ≤ 1)
    {Z : ℕ → ℝ} (hZ : ∀ i : ℕ, 0 ≤ Z i) (hZ0 : Z 0 = 1)
    (henv : ∀ q : ℝ, 1 < q → ∃ M : ℝ, ∀ i : ℕ, Z i ≤ M * q ^ i) :
    ∀ q : ℝ, 1 < q → ∃ M : ℝ, ∀ i : ℕ, contractedZ k Z i ≤ M * q ^ i := by
  intro q hq
  obtain ⟨M, hM⟩ := henv q hq
  have hM1 : 1 ≤ M := by simpa only [hZ0, pow_zero, mul_one] using hM 0
  refine ⟨M, ?_⟩
  intro i
  cases i with
  | zero => simpa only [contractedZ_zero, pow_zero, mul_one] using hM1
  | succ i =>
    have hh := mul_le_mul_of_nonneg_right hk1 (hZ (i + 1))
    calc
      contractedZ k Z (i + 1) = k * Z (i + 1) := rfl
      _ ≤ Z (i + 1) := by simpa only [one_mul] using hh
      _ ≤ M * q ^ (i + 1) := hM (i + 1)

end KLSConstantImprovement.NormalizedScalarInitialContraction

#print axioms KLSConstantImprovement.NormalizedScalarInitialContraction.contracted_recurrence
#print axioms KLSConstantImprovement.NormalizedScalarInitialContraction.contracted_cap
#print axioms KLSConstantImprovement.NormalizedScalarInitialContraction.contracted_envelope

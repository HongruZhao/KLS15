import Mathlib

/-! A reciprocal-linear positive weight has a positive floor after every
geometric rescaling. This standalone draft has not been compiled. It
supplies only a scalar weight instance for the separate orbit wrapper. -/
noncomputable section
namespace KLSConstantImprovement.SubexponentialPolynomialWeight

def reciprocalLinear (d : ℕ) : ℝ := 1/((d : ℝ)+1)

theorem reciprocalLinear_positive (d : ℕ) : 0 < reciprocalLinear d := by
  unfold reciprocalLinear
  positivity

/-- Bernoulli gives a uniform explicit lower constant for every d, including
the finitely many ranks preceding the all-rank generator range. -/
theorem reciprocalLinear_geometric_floor
    (ρ : ℝ) (hρ : 1 < ρ) (d : ℕ) :
    (ρ-1)/ρ ≤ ρ^d/((d : ℝ)+1) := by
  have hρ0 : 0 < ρ := by linarith
  have hd : 0 < (d : ℝ)+1 := by positivity
  have hbern : 1+((d+1 : ℕ) : ℝ)*(ρ-1) ≤ ρ^(d+1) :=
    one_add_mul_sub_le_pow (by linarith : (-1 : ℝ) ≤ ρ) (d+1)
  norm_num only [Nat.cast_add,Nat.cast_one] at hbern
  rw [pow_succ] at hbern
  have hmul : (ρ-1)*((d : ℝ)+1) ≤ ρ^d*ρ := by
    nlinarith only [hbern]
  exact (div_le_div_iff₀ hρ0 hd).2 hmul

/-- The exact lower-weight hypothesis needed for all-rate rescaling, with
the explicit choice tau=(rho-1)/rho. No fixed positive global floor for
the unscaled reciprocal-linear weights is asserted. -/
theorem reciprocalLinear_subexponential_floor :
    ∀ ρ : ℝ, 1 < ρ → ∃ τ : ℝ, 0 < τ ∧
      ∀ d : ℕ, 2 ≤ d → τ ≤ reciprocalLinear d*ρ^d := by
  intro ρ hρ
  refine ⟨(ρ-1)/ρ,div_pos (by linarith) (by linarith),?_⟩
  intro d _hd
  have hh := reciprocalLinear_geometric_floor ρ hρ d
  simpa [reciprocalLinear,div_eq_mul_inv,mul_comm] using hh

/-- Any positive sequence dominating a positive multiple of the reciprocal
linear weight satisfies the same all-rate lower-weight condition. -/
theorem subexponential_floor_of_reciprocalLinear_minorant
    (t : ℕ → ℝ) (κ : ℝ) (hκ : 0 < κ)
    (ht : ∀ d : ℕ, 2 ≤ d → κ*reciprocalLinear d ≤ t d) :
    ∀ ρ : ℝ, 1 < ρ → ∃ τ : ℝ, 0 < τ ∧
      ∀ d : ℕ, 2 ≤ d → τ ≤ t d*ρ^d := by
  intro ρ hρ
  obtain ⟨τ,hτ,hfloor⟩ := reciprocalLinear_subexponential_floor ρ hρ
  refine ⟨κ*τ,mul_pos hκ hτ,?_⟩
  intro d hd
  have hpow : 0 ≤ ρ^d := pow_nonneg (by linarith) d
  calc
    κ*τ ≤ κ*(reciprocalLinear d*ρ^d) :=
      mul_le_mul_of_nonneg_left (hfloor d hd) hκ.le
    _ = (κ*reciprocalLinear d)*ρ^d := by ring
    _ ≤ t d*ρ^d := mul_le_mul_of_nonneg_right (ht d hd) hpow

end KLSConstantImprovement.SubexponentialPolynomialWeight

#print axioms KLSConstantImprovement.SubexponentialPolynomialWeight.reciprocalLinear_positive
#print axioms KLSConstantImprovement.SubexponentialPolynomialWeight.reciprocalLinear_geometric_floor
#print axioms KLSConstantImprovement.SubexponentialPolynomialWeight.reciprocalLinear_subexponential_floor
#print axioms KLSConstantImprovement.SubexponentialPolynomialWeight.subexponential_floor_of_reciprocalLinear_minorant

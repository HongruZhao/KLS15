import Mathlib

/-! Scalar energy step underlying Lemma 7.2 of the supplied deterministic KLS
paper. This module proves a real-number inequality, not a new KLS endpoint. -/

namespace KLSBelow25

theorem ratio_energy_step {r δ rnext : ℝ}
    (hr : 1 < r)
    (henergy : 0 < (r - 1) ^ 2 - 2 * r * δ)
    (hnext : r - δ ≤ rnext) :
    1 < rnext ∧
      (r - 1) ^ 2 - 2 * r * δ ≤ (rnext - 1) ^ 2 - 2 * δ := by
  have hdrop : δ < r - 1 := by
    by_contra h
    have hle : r - 1 ≤ δ := le_of_not_gt h
    have hm := mul_le_mul_of_nonneg_left hle (show 0 ≤ 2 * r by linarith)
    nlinarith
  have hb : 1 < r - δ := by linarith
  have hn : 1 < rnext := by linarith
  refine ⟨hn, ?_⟩
  have hsq : (r - δ - 1) ^ 2 ≤ (rnext - 1) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ rnext - (r - δ) by linarith)
      (show 0 ≤ rnext + (r - δ) - 2 by linarith)]
  nlinarith [sq_nonneg δ]

theorem positive_energy_ratio_gap {r ε z κ : ℝ}
    (hr : 1 < r) (hε : 0 ≤ ε) (hz : 0 < z) (hκ : 0 < κ)
    (he : κ ^ 2 ≤ (r - 1) ^ 2 - 2 * ε / z) :
    1 + κ ≤ r := by
  have hterm : 0 ≤ 2 * ε / z := div_nonneg (by positivity) hz.le
  nlinarith

theorem scalar_energy_step {ε x y w κ : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hκ : 0 < κ)
    (hr : 1 < y / x)
    (he : κ ^ 2 ≤ (y / x - 1) ^ 2 - 2 * ε / x)
    (hw : y ^ 2 / x - ε ≤ w) :
    0 < w ∧ 1 < w / y ∧
      κ ^ 2 ≤ (w / y - 1) ^ 2 - 2 * ε / y := by
  have hcancel : 2 * (y / x) * (ε / y) = 2 * ε / x := by
    field_simp
  have hnext : y / x - ε / y ≤ w / y := by
    apply (le_div_iff₀ hy).2
    have hid : (y / x - ε / y) * y = y ^ 2 / x - ε := by
      field_simp
    rwa [hid]
  have hepos : 0 < (y / x - 1) ^ 2 - 2 * (y / x) * (ε / y) := by
    rw [hcancel]
    exact lt_of_lt_of_le (sq_pos_of_pos hκ) he
  obtain ⟨hwnext, henergy⟩ := ratio_energy_step hr hepos hnext
  have hyw : y < w := by
    have := (lt_div_iff₀ hy).1 hwnext
    simpa using this
  refine ⟨lt_trans hy hyw, hwnext, ?_⟩
  rw [hcancel] at henergy
  simpa only [mul_div_assoc] using he.trans henergy

theorem scalar_sequence_growth {ε κ : ℝ} (hε : 0 ≤ ε) (hκ : 0 < κ)
    (z : ℕ → ℝ) (hz0 : z 0 = 1) (hz1 : 1 < z 1)
    (he0 : κ ^ 2 ≤ (z 1 / z 0 - 1) ^ 2 - 2 * ε / z 0)
    (hrec : ∀ j : ℕ, 0 < z j → 0 < z (j + 1) →
      z (j + 1) ^ 2 / z j - ε ≤ z (j + 2)) :
    ∀ j : ℕ, (1 + κ) ^ j ≤ z j := by
  have hinv : ∀ j : ℕ, 0 < z j ∧ 1 < z (j + 1) / z j ∧
      κ ^ 2 ≤ (z (j + 1) / z j - 1) ^ 2 - 2 * ε / z j := by
    intro j
    induction j with
    | zero =>
        refine ⟨by rw [hz0]; norm_num, ?_, he0⟩
        simpa [hz0] using hz1
    | succ j ih =>
        obtain ⟨hx, hr, he⟩ := ih
        have hy : 0 < z (j + 1) := by
          have hxy := (lt_div_iff₀ hx).1 hr
          nlinarith
        have hs := scalar_energy_step hx hy hκ hr he (hrec j hx hy)
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.reduceAdd] using
          And.intro hy hs.2
  intro j
  induction j with
  | zero => simp [hz0]
  | succ j ih =>
      obtain ⟨hx, hr, he⟩ := hinv j
      have hgap := positive_energy_ratio_gap hr hε hx hκ he
      have hmul : (1 + κ) * z j ≤ z (j + 1) := (le_div_iff₀ hx).1 hgap
      calc
        (1 + κ) ^ (j + 1) = (1 + κ) * (1 + κ) ^ j := by ring
        _ ≤ (1 + κ) * z j := mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ z (j + 1) := hmul

/-- The full real scalar growth lemma from Section 7, including positivity.
Its recurrence is only assumed at positive consecutive entries; positivity
and growth of every entry are conclusions, not hidden hypotheses. -/
theorem scalar_growth_of_initial_gap {ε q : ℝ}
    (hε : 0 < ε) (hq : 0 < q) (hgap : 2 * ε < q ^ 2)
    (z : ℕ → ℝ) (hz0 : z 0 = 1) (hz1 : 1 + q < z 1)
    (hrec : ∀ j : ℕ, 0 < z j → 0 < z (j + 1) →
      z (j + 1) ^ 2 / z j - ε ≤ z (j + 2)) :
    ∀ j : ℕ, 0 < z j ∧
      (1 + Real.sqrt (q ^ 2 - 2 * ε)) ^ j ≤ z j := by
  have hrad : 0 < q ^ 2 - 2 * ε := by linarith
  have hκ : 0 < Real.sqrt (q ^ 2 - 2 * ε) := Real.sqrt_pos.2 hrad
  have hκsq := Real.sq_sqrt hrad.le
  have he0 : (Real.sqrt (q ^ 2 - 2 * ε)) ^ 2 ≤
      (z 1 / z 0 - 1) ^ 2 - 2 * ε / z 0 := by
    rw [hz0]
    simp only [div_one]
    nlinarith
  have hgrowth := scalar_sequence_growth hε.le hκ z hz0
    (by linarith : 1 < z 1) he0 hrec
  intro j
  exact ⟨lt_of_lt_of_le (pow_pos (by linarith) j) (hgrowth j), hgrowth j⟩

#print axioms ratio_energy_step
#print axioms positive_energy_ratio_gap
#print axioms scalar_energy_step
#print axioms scalar_sequence_growth
#print axioms scalar_growth_of_initial_gap

end KLSBelow25

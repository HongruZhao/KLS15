import ScalarNormalization

/-! A finite restart of the scalar spectral contradiction.  This changes no
coefficient envelope and introduces no analytic assumption. -/
noncomputable section
namespace KLSBelow25

theorem scalar_tail_energy_impossible {ε a b : ℝ} (hε : 0 ≤ ε)
    (ha : 0 < a) (hb : 0 < b) (hgap : 2 * ε / a < b ^ 2)
    (z : ℕ → ℝ)
    (hrec : ∀ j : ℕ, 0 < z j → 0 < z (j+1) →
      z (j+1)^2 / z j - ε ≤ z (j+2))
    (henv : ∀ ρ : ℝ, 1 < ρ → ∃ M : ℝ, ∀ j : ℕ, z j ≤ M * ρ^j)
    (N : ℕ) (hza : a ≤ z N) (hzb : 1 + b ≤ z (N+1) / z N) : False := by
  have hz : 0 < z N := lt_of_lt_of_le ha hza
  have hzne := ne_of_gt hz
  let w : ℕ → ℝ := fun j => z (N+j) / z N
  let κ : ℝ := Real.sqrt (b^2 - 2*ε/a)
  have hrad : 0 < b^2 - 2*ε/a := by linarith
  have hκ : 0 < κ := Real.sqrt_pos.2 hrad
  have hκsq : κ^2 = b^2 - 2*ε/a := Real.sq_sqrt hrad.le
  have hw0 : w 0 = 1 := by simp [w, hzne]
  have hw1 : 1 < w 1 := by dsimp [w]; linarith
  have henergy : κ^2 ≤ (w 1 / w 0 - 1)^2 - 2*(ε/z N)/w 0 := by
    rw [hw0]
    simp only [div_one]
    have hdiv : 2*ε/z N ≤ 2*ε/a :=
      div_le_div_of_nonneg_left (by positivity) ha hza
    rw [mul_div_assoc] at hdiv
    have hsq : b^2 ≤ (w 1-1)^2 := by dsimp [w]; nlinarith
    rw [hκsq]
    linarith
  have hwrec : ∀ j : ℕ, 0 < w j → 0 < w (j+1) →
      w (j+1)^2/w j - ε/z N ≤ w (j+2) := by
    intro j hj hj1
    have hj' : 0 < z (N+j) := (div_pos_iff_of_pos_right hz).mp hj
    have hj1' : 0 < z (N+j+1) := by
      have := (div_pos_iff_of_pos_right hz).mp hj1
      simpa [w, Nat.add_assoc] using this
    have hr := div_le_div_of_nonneg_right (hrec (N+j) hj' hj1') hz.le
    have hid : (z (N+j+1)^2/z (N+j)-ε)/z N =
        w (j+1)^2/w j-ε/z N := by
      dsimp [w]
      simp only [Nat.add_assoc]
      field_simp
    rw [hid] at hr
    simpa [w, Nat.add_assoc] using hr
  have hgrowth := scalar_sequence_growth (div_nonneg hε hz.le) hκ w hw0 hw1 henergy hwrec
  let ρ : ℝ := 1 + κ/2
  have hρ : 1 < ρ := by dsimp [ρ]; linarith
  obtain ⟨M,hM⟩ := henv ρ hρ
  have hwenv : ∀ j : ℕ, w j ≤ (M * ρ^N / z N) * ρ^j := by
    intro j
    have := div_le_div_of_nonneg_right (hM (N+j)) hz.le
    calc
      w j ≤ M * ρ^(N+j) / z N := this
      _ = (M * ρ^N / z N) * ρ^j := by rw [pow_add]; ring
  exact no_growth_above_exponential_envelope (by linarith : 0 < ρ)
    (by dsimp [ρ]; linarith : ρ < 1+κ) hgrowth hwenv

/-- A rational table of lower bounds on the orbit and its successive ratios
is enough to restart the growth contradiction at its final row. -/
theorem scalar_finite_bootstrap_impossible {ε : ℝ} (hε : 0 ≤ ε)
    (N : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ j ≤ N, 0 < a j) (hb : ∀ j ≤ N, 0 < b j)
    (ha0 : a 0 = 1)
    (hstepa : ∀ j < N, a (j+1) ≤ a j * (1+b j))
    (hstepb : ∀ j < N, b (j+1) ≤ b j - ε/a (j+1))
    (hgap : 2*ε/a N < (b N)^2)
    (z : ℕ → ℝ) (hz0 : z 0 = 1) (hz1 : 1+b 0 ≤ z 1)
    (hrec : ∀ j : ℕ, 0 < z j → 0 < z (j+1) →
      z (j+1)^2/z j - ε ≤ z (j+2))
    (henv : ∀ ρ : ℝ, 1 < ρ → ∃ M : ℝ, ∀ j : ℕ, z j ≤ M * ρ^j) : False := by
  have hinv : ∀ j ≤ N, a j ≤ z j ∧ 1+b j ≤ z (j+1)/z j := by
    intro j
    induction j with
    | zero =>
        intro hj
        constructor
        · rw [ha0, hz0]
        · simpa [hz0] using hz1
    | succ j ih =>
        intro hj
        have hjN : j < N := Nat.lt_of_succ_le hj
        obtain ⟨hza,hzb⟩ := ih (Nat.le_of_lt hjN)
        have hapos := ha j (Nat.le_of_lt hjN)
        have hbpos := hb j (Nat.le_of_lt hjN)
        have hzpos : 0 < z j := lt_of_lt_of_le hapos hza
        have hmul : z j * (1+b j) ≤ z (j+1) := by
          have := (le_div_iff₀ hzpos).mp hzb
          simpa [mul_comm] using this
        have hzanext : a (j+1) ≤ z (j+1) := by
          calc
            a (j+1) ≤ a j * (1+b j) := hstepa j hjN
            _ ≤ z j * (1+b j) := mul_le_mul_of_nonneg_right hza (by linarith)
            _ ≤ z (j+1) := hmul
        have hznext : 0 < z (j+1) := lt_of_lt_of_le (ha (j+1) hj) hzanext
        have hratio : z (j+1)/z j-ε/z (j+1) ≤ z (j+2)/z (j+1) := by
          apply (le_div_iff₀ hznext).mpr
          have hid : (z (j+1)/z j-ε/z (j+1))*z (j+1) =
              z (j+1)^2/z j-ε := by field_simp
          rw [hid]
          exact hrec j hzpos hznext
        have hdrop : ε/z (j+1) ≤ ε/a (j+1) :=
          div_le_div_of_nonneg_left hε (ha (j+1) hj) hzanext
        have hbn := hstepb j hjN
        refine ⟨hzanext, ?_⟩
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.reduceAdd] using
          (show 1+b (j+1) ≤ z (j+2)/z (j+1) by linarith)
  obtain ⟨hza,hzb⟩ := hinv N le_rfl
  exact scalar_tail_energy_impossible hε (ha N le_rfl) (hb N le_rfl)
    hgap z hrec henv N hza hzb

#print axioms scalar_tail_energy_impossible
#print axioms scalar_finite_bootstrap_impossible
end KLSBelow25

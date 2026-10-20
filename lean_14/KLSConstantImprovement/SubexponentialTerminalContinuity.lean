import KLSConstantImprovement.SubexponentialTerminalSupremum

/-! The actual positive terminal supremum is globally Lipschitz.  This
discharges the continuity required in finite-horizon compact minimization
and closed prefix-budget sublevel sets. -/
noncomputable section
namespace KLSConstantImprovement.SubexponentialTerminalContinuity
open KLSConstantImprovement.SubexponentialTerminalSupremum

theorem term_le_add_abs {w : ℕ → ℝ} (p : Floor w) (i : ℕ) (x y : ℝ) :
    p.term i x ≤ p.term i y+w i * |x-y| := by
  have hmax : max 0 (x-p.rate) ≤ max 0 (y-p.rate) + |x-y| := by
    apply max_le
    · exact add_nonneg (le_max_left _ _) (abs_nonneg _)
    · linarith [le_abs_self (x-y),le_max_right 0 (y-p.rate)]
  have hh := mul_le_mul_of_nonneg_left hmax (p.coeff_nonneg i)
  have hw := mul_le_mul_of_nonneg_right (p.coeff_le i) (abs_nonneg (x-y))
  unfold Floor.term GeometricBellmanTerminal.B
  nlinarith only [hh,hw]

theorem terminalSup_le_add_abs {w : ℕ → ℝ} (hF : Nonempty (Floor w))
    (i : ℕ) (x y : ℝ) : terminalSup w i x ≤ terminalSup w i y+w i * |x-y| := by
  obtain ⟨p0⟩ := hF
  apply csSup_le (show (Set.range (fun p : Floor w=>p.term i x)).Nonempty from
    ⟨p0.term i x,⟨p0,rfl⟩⟩)
  rintro z ⟨p,rfl⟩
  exact (term_le_add_abs p i x y).trans
    (add_le_add (term_le_sup p i y) (le_refl _))

theorem terminalSup_lipschitz {w : ℕ → ℝ} (hF : Nonempty (Floor w)) (i : ℕ) :
    LipschitzWith (Real.toNNReal (w i)) (terminalSup w i) := by
  apply LipschitzWith.of_le_add_mul' (w i)
  intro x y
  simpa only [Real.dist_eq] using terminalSup_le_add_abs hF i x y

theorem terminalSup_continuous {w : ℕ → ℝ} (hF : Nonempty (Floor w)) (i : ℕ) :
    Continuous (terminalSup w i) := (terminalSup_lipschitz hF i).continuous

theorem terminalSup_monotone {w : ℕ → ℝ} (hF : Nonempty (Floor w)) (i : ℕ) :
    Monotone (terminalSup w i) := by
  intro x y hxy
  obtain ⟨p0⟩ := hF
  apply csSup_le (show (Set.range (fun p : Floor w=>p.term i x)).Nonempty from
    ⟨p0.term i x,⟨p0,rfl⟩⟩)
  rintro z ⟨p,rfl⟩
  have hh : p.term i x ≤ p.term i y :=
    mul_le_mul_of_nonneg_left (max_le_max_left 0 (by linarith)) (p.coeff_nonneg i)
  exact hh.trans (term_le_sup p i y)

theorem terminalSup_zero {w : ℕ → ℝ} (hF : Nonempty (Floor w))
    (i : ℕ) {r : ℝ} (hr : r ≤ 1) : terminalSup w i r=0 := by
  have hh := terminalSup_le hF i r
  rw [max_eq_left (by linarith : r-1 ≤ 0),mul_zero] at hh
  exact le_antisymm hh (terminalSup_nonneg hF i r)

end KLSConstantImprovement.SubexponentialTerminalContinuity
#print axioms KLSConstantImprovement.SubexponentialTerminalContinuity.terminalSup_lipschitz
#print axioms KLSConstantImprovement.SubexponentialTerminalContinuity.terminalSup_continuous
#print axioms KLSConstantImprovement.SubexponentialTerminalContinuity.terminalSup_monotone
#print axioms KLSConstantImprovement.SubexponentialTerminalContinuity.terminalSup_zero

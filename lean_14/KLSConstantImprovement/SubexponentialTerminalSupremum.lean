import KLSConstantImprovement.GeometricBellmanTerminal
import KLSConstantImprovement.GeometricWeightedTailPayment
import KLSConstantImprovement.GeneralSubexponentialWeightedObservation

/-! The finite positive terminal family for general subexponential inverse
weights. Its real supremum is bounded, is a Bellman subsolution, and is
paid by the actual normalized orbit. Infinite minimum attainment and the
outer profile optimization are not claimed in this module. -/
noncomputable section
namespace KLSConstantImprovement.SubexponentialTerminalSupremum
open KLSConstantImprovement.WeightedOrbitBellmanTail

structure Floor (w : ℕ → ℝ) where
  rate : ℝ
  amount : ℝ
  rate_gt_one : 1 < rate
  amount_pos : 0 < amount
  lower : ∀ i,amount ≤ w i*rate^(i+2)

def Floor.coeff {w : ℕ → ℝ} (p : Floor w) (i : ℕ) : ℝ := p.amount/p.rate^(i+2)
def Floor.term {w : ℕ → ℝ} (p : Floor w) (i : ℕ) (r : ℝ) : ℝ :=
  GeometricBellmanTerminal.B (p.coeff i) p.rate r
def terminalSup (w : ℕ → ℝ) (i : ℕ) (r : ℝ) : ℝ :=
  sSup (Set.range (fun p : Floor w=>p.term i r))

theorem Floor.coeff_nonneg {w : ℕ → ℝ} (p : Floor w) (i : ℕ) : 0 ≤ p.coeff i := by
  exact div_nonneg p.amount_pos.le (pow_nonneg (by linarith [p.rate_gt_one]) _)

theorem Floor.coeff_le {w : ℕ → ℝ} (p : Floor w) (i : ℕ) : p.coeff i ≤ w i := by
  exact (div_le_iff₀ (pow_pos (by linarith [p.rate_gt_one]) _)).mpr (p.lower i)

theorem Floor.term_nonneg {w : ℕ → ℝ} (p : Floor w) (i : ℕ) (r : ℝ) :
    0 ≤ p.term i r := GeometricBellmanTerminal.B_nonnegative (p.coeff_nonneg i)

theorem Floor.term_le {w : ℕ → ℝ} (p : Floor w) (i : ℕ) (r : ℝ) :
    p.term i r ≤ w i*max 0 (r-1) := by
  have hw : 0 ≤ w i := (p.coeff_nonneg i).trans (p.coeff_le i)
  have hm : max 0 (r-p.rate) ≤ max 0 (r-1) :=
    max_le_max_left 0 (by linarith [p.rate_gt_one])
  exact mul_le_mul (p.coeff_le i) hm (le_max_left _ _) hw

theorem terminal_range_bounded (w : ℕ → ℝ) (i : ℕ) (r : ℝ) :
    BddAbove (Set.range (fun p : Floor w=>p.term i r)) := by
  refine ⟨w i*max 0 (r-1),?_⟩
  rintro y ⟨p,rfl⟩
  exact p.term_le i r

theorem term_le_sup {w : ℕ → ℝ} (p : Floor w) (i : ℕ) (r : ℝ) :
    p.term i r ≤ terminalSup w i r :=
  le_csSup (terminal_range_bounded w i r) ⟨p,rfl⟩

theorem terminalSup_nonneg {w : ℕ → ℝ} (hF : Nonempty (Floor w)) (i : ℕ) (r : ℝ) :
    0 ≤ terminalSup w i r := by
  obtain ⟨p⟩ := hF
  exact (p.term_nonneg i r).trans (term_le_sup p i r)

theorem terminalSup_le {w : ℕ → ℝ} (hF : Nonempty (Floor w)) (i : ℕ) (r : ℝ) :
    terminalSup w i r ≤ w i*max 0 (r-1) := by
  obtain ⟨p⟩ := hF
  apply csSup_le (show (Set.range (fun q : Floor w=>q.term i r)).Nonempty from ⟨p.term i r,⟨p,rfl⟩⟩)
  rintro y ⟨q,rfl⟩
  exact q.term_le i r

theorem Floor.coeff_succ {w : ℕ → ℝ} (p : Floor w) (i : ℕ) :
    p.coeff (i+1)=p.coeff i/p.rate := by
  unfold Floor.coeff
  have hρ : p.rate≠0 := ne_of_gt (by linarith [p.rate_gt_one])
  simp only [pow_succ]
  field_simp [hρ] <;> ring

/-- The supremum of all geometric terminals is itself a Bellman
subsolution, including rising next ratios and ratios below one. -/
theorem terminalSup_step {w : ℕ → ℝ} (hF : Nonempty (Floor w))
    (i : ℕ) {r s d : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d) (hdrop : r-s ≤ d) :
    terminalSup w i r ≤ w i*d+s*terminalSup w (i+1) s := by
  obtain ⟨p0⟩ := hF
  apply csSup_le (show (Set.range (fun p : Floor w=>p.term i r)).Nonempty from ⟨p0.term i r,⟨p0,rfl⟩⟩)
  rintro y ⟨p,rfl⟩
  have hh := GeometricBellmanTerminal.terminal_step
    (show 0 < p.rate by linarith [p.rate_gt_one])
    (p.coeff_nonneg i) (p.coeff_le i) hs hd hdrop
  rw [←p.coeff_succ i] at hh
  exact hh.trans (add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left (term_le_sup p (i+1) s) hs))

/-- The entire positive terminal family is paid by the same actual
normalized orbit and budget. No uniform positive weight floor is used. -/
theorem terminalSup_payment (Z c w : ℕ → ℝ) {C : ℝ} (hF : Nonempty (Floor w))
    (hZ : ∀ i,0 ≤ Z i) (hc : ∀ i,0 ≤ c i)
    (hzero : ∀ i,Z i=0 → Z (i+1)=0)
    (hrec : ∀ i,0 < Z i → 0 < Z (i+1) →
      Z (i+1)^2/Z i-c i ≤ Z (i+2))
    (hbudget : ∀ j,spend w c j ≤ C)
    (henv : ∀ q : ℝ,1 < q → ∃ M : ℝ,∀ i,Z i ≤ M*q^i) (N : ℕ) :
    Z (N+1)*terminalSup w N (Z (N+1)/Z N) ≤ C-spend w c N := by
  have hrem : 0 ≤ C-spend w c N := by linarith [hbudget N]
  by_cases hz0 : Z (N+1)=0
  · rw [hz0,zero_mul]
    exact hrem
  have hz : 0 < Z (N+1) := lt_of_le_of_ne (hZ _) (Ne.symm hz0)
  have hs : terminalSup w N (Z (N+1)/Z N) ≤ (C-spend w c N)/Z (N+1) := by
    obtain ⟨p0⟩ := hF
    apply csSup_le (show (Set.range (fun p : Floor w=>p.term N (Z (N+1)/Z N))).Nonempty from
      ⟨p0.term N (Z (N+1)/Z N),⟨p0,rfl⟩⟩)
    rintro y ⟨p,rfl⟩
    have hh := GeometricWeightedTailPayment.geometric_tail_payment Z c w N
      p.amount_pos p.rate_gt_one hZ hc hzero hrec (fun i _=>p.lower i) hbudget henv
    have he : max 0 (p.coeff N*(Z (N+1)/Z N-p.rate))=
        p.term N (Z (N+1)/Z N) := by
      unfold Floor.term GeometricBellmanTerminal.B
      rw [mul_max_of_nonneg 0 _ (p.coeff_nonneg N),mul_zero]
    change Z (N+1)*max 0 (p.coeff N*(Z (N+1)/Z N-p.rate)) ≤ C-spend w c N at hh
    rw [he] at hh
    exact (le_div_iff₀ hz).mpr (by simpa only [mul_comm] using hh)
  simpa only [mul_comm] using (le_div_iff₀ hz).mp hs

end KLSConstantImprovement.SubexponentialTerminalSupremum
#print axioms KLSConstantImprovement.SubexponentialTerminalSupremum.terminalSup_le
#print axioms KLSConstantImprovement.SubexponentialTerminalSupremum.terminalSup_step
#print axioms KLSConstantImprovement.SubexponentialTerminalSupremum.terminalSup_payment

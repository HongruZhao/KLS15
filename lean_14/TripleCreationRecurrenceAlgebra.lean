import PairProjectionCreationBound

/-! Scalar certificate for the proposed fourth-cumulant triple-insertion
recurrence. This file proves no actual tensor overlap or cumulant estimate. -/
noncomputable section
namespace KLSBelow25.TripleCreation
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def chooseThree (n : ℝ) : ℝ := n*(n-1)*(n-2)/6

def forcing (L n : ℝ) : ℝ :=
  L*n*(n-1)*(n-2)*(3*n-8)/6 +
    9*n*(n-1)*(n-2)*(n-3)*(n-4)

def recurrenceMultiplier (n : ℝ) : ℝ :=
  n*(n-1)*(n-5)/((n-2)*(n-3)*(n-4))

def closed (L n : ℝ) : ℝ :=
  36*(chooseThree n)^2 +
    (L-36)/210*n*(n-1)*(n-2)*(15*n^2-26*n+4)

theorem closed_three (L : ℝ) : closed L 3-L=26*(L-36)/35 := by
  unfold closed chooseThree
  ring

theorem closed_four (L : ℝ) : closed L 4=16*L := by
  unfold closed chooseThree
  ring

theorem closed_recurrence_identity (L n : ℝ) (hn : 5 ≤ n) :
    closed L n - forcing L n - recurrenceMultiplier n*closed L (n-2) =
      2*(L-36)*n*(n-1)/35 := by
  have h2 : n-2 ≠ 0 := by linarith
  have h3 : n-3 ≠ 0 := by linarith
  have h4 : n-4 ≠ 0 := by linarith
  unfold closed forcing recurrenceMultiplier chooseThree
  field_simp
  ring

theorem recurrenceMultiplier_nonneg (n : ℝ) (hn : 5 ≤ n) :
    0 ≤ recurrenceMultiplier n := by
  unfold recurrenceMultiplier
  apply div_nonneg
  · exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  · exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)

theorem closed_recurrence_ge {L n : ℝ} (hL : 36 ≤ L) (hn : 5 ≤ n) :
    forcing L n + recurrenceMultiplier n*closed L (n-2) ≤ closed L n := by
  have he := closed_recurrence_identity L n hn
  have hL0 : 0 ≤ L-36 := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hn1 : 0 ≤ n-1 := by linarith
  have hp : 0 ≤ 2*(L-36)*n*(n-1)/35 := by positivity
  linarith

theorem closed_nonneg {L n : ℝ} (hL : 36 ≤ L) (hn : 3 ≤ n) :
    0 ≤ closed L n := by
  have hp : 0 ≤ 15*n^2-26*n+4 := by nlinarith [sq_nonneg (n-3)]
  have hL0 : 0 ≤ L-36 := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hn1 : 0 ≤ n-1 := by linarith
  have hn2 : 0 ≤ n-2 := by linarith
  unfold closed
  positivity

/-- Absorption of an honest step-two recurrence; no sign condition on the
sequence itself is needed. Tensor estimates must supply `hstep` separately. -/
theorem sequence_le_closed (L : ℝ) (x : ℕ → ℝ) (hL : 36 ≤ L)
    (hthree : x 3 ≤ L) (hfour : x 4 ≤ 16*L)
    (hstep : ∀ n : ℕ, 5 ≤ n →
      x n ≤ forcing L n + recurrenceMultiplier n*x (n-2)) :
    ∀ n : ℕ, 3 ≤ n → x n ≤ closed L n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases h3 : n=3
    · subst n
      have he := closed_three L
      have hp : 0 ≤ 26*(L-36)/35 := by positivity
      norm_num only [Nat.cast_ofNat]
      linarith
    by_cases h4 : n=4
    · subst n
      simpa only [Nat.cast_ofNat,closed_four] using hfour
    have hn5 : 5 ≤ n := by omega
    have hnreal : (5 : ℝ) ≤ n := by exact_mod_cast hn5
    have hprev := ih (n-2) (by omega) (by omega : 3 ≤ n-2)
    have hcast : ((n-2 : ℕ) : ℝ)=(n : ℝ)-2 := by
      exact Nat.cast_sub (by omega : 2 ≤ n)
    calc
      x n ≤ forcing L n + recurrenceMultiplier n*x (n-2) := hstep n hn5
      _ ≤ forcing L n + recurrenceMultiplier n*closed L (n-2 : ℕ) :=
        by
          simpa only [add_comm] using add_le_add_left
            (mul_le_mul_of_nonneg_left hprev
              (recurrenceMultiplier_nonneg n hnreal)) (forcing L n)
      _ = forcing L n + recurrenceMultiplier n*closed L ((n : ℝ)-2) := by rw [hcast]
      _ ≤ closed L n := closed_recurrence_ge hL hnreal

/-- The factorial normalization for an output of degree `n` and input `n-2`.
The leading normalized creation square is `(n-2)^2 / K^2`. -/
theorem normalized_closed_identity (L K n : ℝ) (hK : K ≠ 0) (hn : 3 ≤ n) :
    closed L n/(K^2*n^2*(n-1)^2) =
      (n-2)^2/K^2 +
      (L-36)*(n-2)*(15*n^2-26*n+4)/(210*K^2*n*(n-1)) := by
  have hn0 : n ≠ 0 := by linarith
  have hn1 : n-1 ≠ 0 := by linarith
  unfold closed chooseThree
  field_simp
  ring

end KLSBelow25.TripleCreation
#print axioms KLSBelow25.TripleCreation.closed_recurrence_identity
#print axioms KLSBelow25.TripleCreation.sequence_le_closed
#print axioms KLSBelow25.TripleCreation.normalized_closed_identity

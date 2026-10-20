import TripleCreationRecurrenceAlgebra

/-! Exact recursive cap, retaining the finite degrees before the closed
supersolution is used. -/
noncomputable section
namespace KLSBelow25.TripleCreation
set_option maxHeartbeats 1200000

def exactCap : ℕ→ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 864
  | 4 => 13824
  | n+5 => forcing 864 ((n:ℝ)+5)+recurrenceMultiplier ((n:ℝ)+5)*exactCap (n+3)
termination_by n => n

@[simp] theorem exactCap_three : exactCap 3=864 := by rw [exactCap]
@[simp] theorem exactCap_four : exactCap 4=13824 := by rw [exactCap]

theorem exactCap_step (n : ℕ) (hn : 5≤n) :
    exactCap n=forcing 864 n+recurrenceMultiplier n*exactCap (n-2) := by
  obtain ⟨k,rfl⟩ : ∃k,n=k+5 := ⟨n-5,by omega⟩
  rw [exactCap]
  simp only [Nat.cast_add,Nat.cast_ofNat]
  congr 2

theorem exactCap_nonneg (n : ℕ) : 0≤exactCap n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : 5≤n
    · rw [exactCap_step n hn]
      have hnr : (5:ℝ)≤n := by exact_mod_cast hn
      have hp : 0≤forcing 864 n := by
        unfold forcing
        have h0 : 0≤(n:ℝ) := by positivity
        have h1 : 0≤(n:ℝ)-1 := by linarith
        have h2 : 0≤(n:ℝ)-2 := by linarith
        have h3 : 0≤(n:ℝ)-3 := by linarith
        have h4 : 0≤(n:ℝ)-4 := by linarith
        have h5 : 0≤3*(n:ℝ)-8 := by linarith
        positivity
      exact add_nonneg hp (mul_nonneg (recurrenceMultiplier_nonneg n hnr)
        (ih (n-2) (by omega)))
    · interval_cases n <;> norm_num [exactCap]

theorem exactCap_le_closed (n : ℕ) (hn : 3≤n) : exactCap n≤closed 864 n :=
  sequence_le_closed 864 exactCap (by norm_num) (by norm_num) (by norm_num)
    (fun n hn=>le_of_eq (exactCap_step n hn)) n hn

end KLSBelow25.TripleCreation
#print axioms KLSBelow25.TripleCreation.exactCap_nonneg
#print axioms KLSBelow25.TripleCreation.exactCap_le_closed

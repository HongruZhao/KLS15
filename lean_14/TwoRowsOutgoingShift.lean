import ActualHarmonicCenteredAppellDrift
import ActualHarmonicTripleAppellDrift

/-! Positive outgoing costs reindex into the original full energy sum. -/
noncomputable section
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLSBelow25.TripleCreation
set_option maxHeartbeats 1500000

theorem sum_two_previous_degrees_le (N : ℕ) (F : ℕ → ℝ)
    (hF : ∀ b ∈ Finset.Icc 2 N, 0 ≤ F b) :
    (∑ d ∈ Finset.Icc 3 N, if 4 ≤ d then F (d-2) else 0) ≤ ∑ b ∈ Finset.Icc 2 N, F b := by
  classical
  have he : (∑ d ∈ Finset.Icc 4 N, F (d-2)) =
      ∑ d ∈ Finset.Icc 3 N, if 4 ≤ d then F (d-2) else 0 := by
    calc
      _ = ∑ d ∈ Finset.Icc 4 N, if 4 ≤ d then F (d-2) else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [ite_eq_left (Finset.mem_Icc.mp hd).1]
      _ = _ := by
        apply Finset.sum_subset (by intro d hd; simp only [Finset.mem_Icc] at hd ⊢;omega)
        intro d hd hn
        have hh : ¬4 ≤ d := by simp only [Finset.mem_Icc] at hd hn;omega
        rw [ite_eq_right hh]
  rw [←he]
  have hinj : Set.InjOn (fun d : ℕ => d-2) (Finset.Icc 4 N : Set ℕ) := by
    intro d hd e he hde
    simp only [Finset.mem_coe,Finset.mem_Icc] at hd he
    dsimp only at hde
    omega
  have hsub : (Finset.Icc 4 N).image (fun d : ℕ => d-2) ⊆ Finset.Icc 2 N := by
    intro b hb
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hb
    simp only [Finset.mem_Icc] at hd ⊢
    omega
  calc
    _ = ∑ b ∈ (Finset.Icc 4 N).image (fun d : ℕ => d-2), F b := (Finset.sum_image hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun b hb _ => hF b hb)

theorem triple_affine_rest_nonneg_nat (b : ℕ) (hb : 2 ≤ b) :
    0 ≤ affineRest (exactCap b) ((b : ℝ)+2) := by
  by_cases h2 : b=2
  · subst b
    norm_num [affineRest,recurrenceMultiplier]
  have hbc : (3 : ℝ) ≤ b := by exact_mod_cast (show 3 ≤ b by omega)
  have hm := recurrenceMultiplier_nonneg ((b : ℝ)+2) (by linarith)
  have hB := exactCap_nonneg b
  have h0 : 0 ≤ (b : ℝ)+2 := by linarith
  have h1 : 0 ≤ (b : ℝ)+2-1 := by linarith
  have h2 : 0 ≤ (b : ℝ)+2-2 := by linarith
  have h3 : 0 ≤ (b : ℝ)+2-3 := by linarith
  have h4 : 0 ≤ (b : ℝ)+2-4 := by linarith
  unfold affineRest
  positivity

theorem tripleHarmonicNeighborCharge_nonneg {K : ℝ} (hK : 0 < K)
    (s zeta : ℕ → ℝ) (b : ℕ) (hb : 2 ≤ b) (hs : 0 < s b) (hz : 0 ≤ zeta b) :
    0 ≤ tripleHarmonicNeighborCharge K s zeta b := by
  unfold tripleHarmonicNeighborCharge
  exact div_nonneg (mul_nonneg hz (triple_affine_rest_nonneg_nat b hb)) (by positivity)

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.sum_two_previous_degrees_le
#print axioms KLS.DeterministicBridgeNext.tripleHarmonicNeighborCharge_nonneg

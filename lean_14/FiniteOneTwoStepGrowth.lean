import Mathlib
noncomputable section
namespace KLSBelow25.ProjectionSlackRatio

/-- A finite one/two-step anchor scheme produces uniform exponential
amplitude growth, including the possible unpaired final downward step. -/
theorem finite_one_two_step_growth
    (z : ℕ → ℝ) (l V gamma : ℝ) (hl : 0 < l) (hl1 : l ≤ 1)
    (hV : 0 < V) (hgamma : 1 ≤ gamma) (hinit : V ≤ z 2)
    (hstep : ∀ m,2 ≤ m  →  (∀ i,2 ≤ i  →  i ≤ m  →  l*V ≤ z i)  →  V ≤ z m  → 
      l*z m ≤ z (m+1) ∧
        (gamma*z m ≤ z (m+1) ∨ gamma^2*z m ≤ z (m+2))) :
    ∀ k,l*V*gamma^k ≤ z (k+3) := by
  have hp : ∀ k, 1 ≤ gamma^k := fun k=>one_le_pow₀ hgamma
  have hs : ∀ k, (∀ i,2 ≤ i  →  i ≤ k+2  →  l*V ≤ z i) ∧
      (V*gamma^k ≤ z (k+2) ∨
        (l*V*gamma^(k-1) ≤ z (k+2) ∧ V*gamma^(k+1) ≤ z (k+3))) := by
    intro k
    induction k with
    | zero =>
      constructor
      · intro i hi hi2
        have he : i=2 := by omega
        subst i
        exact (by nlinarith : l*V ≤ V).trans hinit
      · left
        simpa using hinit
    | succ k ih =>
      rcases ih with ⟨hfloor,hstate⟩
      rcases hstate with hstrong | hweak
      · have hanchor : V ≤ z (k+2) := (by nlinarith [hp k] : V ≤ V*gamma^k).trans hstrong
        obtain ⟨hfnext,hnext⟩ := hstep (k+2) (by omega) hfloor hanchor
        have hf : l*V ≤ z (k+3) := (mul_le_mul_of_nonneg_left hanchor hl.le).trans hfnext
        constructor
        · intro i hi him
          by_cases he : i=k+3
          · simpa [he] using hf
          · exact hfloor i hi (by omega)
        · rcases hnext with hone | htwo
          · left
            have hh := mul_le_mul_of_nonneg_left hstrong (by linarith : 0 ≤ gamma)
            rw [pow_succ]
            nlinarith
          · right
            constructor
            · simpa [mul_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (mul_le_mul_of_nonneg_left hstrong hl.le).trans hfnext
            · have hh := mul_le_mul_of_nonneg_left hstrong (sq_nonneg gamma)
              rw [show k+1+1=k+2 by omega,pow_add]
              nlinarith
      · have hstrong : V*gamma^(k+1) ≤ z (k+3) := hweak.2
        have hf : l*V ≤ z (k+3) := by nlinarith [hp (k+1)]
        constructor
        · intro i hi him
          by_cases he : i=k+3
          · simpa [he] using hf
          · exact hfloor i hi (by omega)
        · exact Or.inl hstrong
  intro k
  have hh := (hs (k+1)).2
  rcases hh with hstrong | hweak
  · have hpow : 0 ≤ gamma^k := (hp k).trans' (by norm_num)
    have hh : l*V*gamma^k ≤ V*gamma^(k+1) := by
      rw [pow_succ]
      nlinarith [mul_nonneg hV.le hpow]
    simpa [Nat.add_assoc] using hh.trans hstrong
  · simpa using hweak.1

end KLSBelow25.ProjectionSlackRatio
#print axioms KLSBelow25.ProjectionSlackRatio.finite_one_two_step_growth

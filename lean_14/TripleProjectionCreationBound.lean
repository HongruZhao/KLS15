import TripleProjectionHilbert

/-! The exact two-step triple-creation recurrence. The four premises retain
the different overlap channels; in particular the two-overlap bound is L,
not the flat-two-operator constant 36. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace KLSBelow25.TripleProjection
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem sumTriples_sq_le_three (U : Triple 3 → H) {Q₃ Q₂ Q₁ Q₀ L E : ℝ}
    (h : Gram U Q₃ Q₂ Q₁ Q₀) (hQ : Q₃≤L*E) :
    ‖sumTriples U‖^2≤L*E := by
  rw [sumTriples_sq_expanded U h (by norm_num)]
  norm_num
  exact hQ

theorem sumTriples_sq_le_four (U : Triple 4 → H) {Q₃ Q₂ Q₁ Q₀ L E : ℝ}
    (h : Gram U Q₃ Q₂ Q₁ Q₀) (hQ₃ : Q₃≤L*E) (hQ₂ : Q₂≤L*E) :
    ‖sumTriples U‖^2≤16*L*E := by
  rw [sumTriples_sq_expanded U h (by norm_num)]
  norm_num
  linarith

theorem disjoint_coefficient_identity (hN : 5≤N) (B : ℝ) :
    ((N : ℝ)*(N-1)*(N-2)*(N-3)*(N-4)*(N-5)/36)*
      (B/(((N-2).choose 3 : ℝ)^2)) =
    ((N : ℝ)*(N-1)*(N-5)/((N-2)*(N-3)*(N-4)))*B := by
  have hn : (5 : ℝ)≤N := by exact_mod_cast hN
  have hchoose : ((N-2).choose 3 : ℝ)=(N-2)*(N-3)*(N-4)/6 := by
    rw [KLSBelow25.PairProjection.cast_choose_three (by omega),
      Nat.cast_sub (by omega : 2≤N)]
    norm_num only [Nat.cast_ofNat]
    ring
  rw [hchoose]
  have h₂ : (N : ℝ)-2≠0 := by linarith
  have h₃ : (N : ℝ)-3≠0 := by linarith
  have h₄ : (N : ℝ)-4≠0 := by linarith
  field_simp [h₂,h₃,h₄]
  ring

theorem sumTriples_sq_le_recurrence (U : Triple N → H)
    {Q₃ Q₂ Q₁ Q₀ L E B : ℝ} (h : Gram U Q₃ Q₂ Q₁ Q₀) (hN : 5≤N)
    (hQ₃ : Q₃≤L*E) (hQ₂ : Q₂≤L*E) (hQ₁ : Q₁≤36*E)
    (hQ₀ : Q₀≤(B/(((N-2).choose 3 : ℝ)^2))*E) :
    ‖sumTriples U‖^2 ≤
      (L*(N : ℝ)*(N-1)*(N-2)*(3*N-8)/6 +
       9*(N : ℝ)*(N-1)*(N-2)*(N-3)*(N-4) +
       ((N : ℝ)*(N-1)*(N-5)/((N-2)*(N-3)*(N-4)))*B)*E := by
  have hn : (5 : ℝ)≤N := by exact_mod_cast hN
  have h₀ : 0≤(N : ℝ) := Nat.cast_nonneg _
  have h₁ : 0≤(N : ℝ)-1 := by linarith
  have h₂ : 0≤(N : ℝ)-2 := by linarith
  have h₃ : 0≤(N : ℝ)-3 := by linarith
  have h₄ : 0≤(N : ℝ)-4 := by linarith
  have h₅ : 0≤(N : ℝ)-5 := by linarith
  have a := mul_le_mul_of_nonneg_left hQ₃
    (div_nonneg (mul_nonneg (mul_nonneg h₀ h₁) h₂) (by norm_num : (0:ℝ)≤6))
  have b := mul_le_mul_of_nonneg_left hQ₂
    (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h₀ h₁) h₂) h₃)
      (by norm_num : (0:ℝ)≤2))
  have c := mul_le_mul_of_nonneg_left hQ₁
    (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h₀ h₁) h₂) h₃) h₄)
      (by norm_num : (0:ℝ)≤4))
  have d := mul_le_mul_of_nonneg_left hQ₀
    (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h₀ h₁)
      h₂) h₃) h₄) h₅) (by norm_num : (0:ℝ)≤36))
  have hd := disjoint_coefficient_identity hN B
  have heq :
      ((N : ℝ)*(N-1)*(N-2)/6)*(L*E)+
      ((N : ℝ)*(N-1)*(N-2)*(N-3)/2)*(L*E)+
      ((N : ℝ)*(N-1)*(N-2)*(N-3)*(N-4)/4)*(36*E)+
      ((N : ℝ)*(N-1)*(N-2)*(N-3)*(N-4)*(N-5)/36)*
        ((B/(((N-2).choose 3 : ℝ)^2))*E) =
      (L*(N : ℝ)*(N-1)*(N-2)*(3*N-8)/6 +
       9*(N : ℝ)*(N-1)*(N-2)*(N-3)*(N-4) +
       ((N : ℝ)*(N-1)*(N-5)/((N-2)*(N-3)*(N-4)))*B)*E := by
    calc
      _ = ((N : ℝ)*(N-1)*(N-2)/6)*(L*E)+
        ((N : ℝ)*(N-1)*(N-2)*(N-3)/2)*(L*E)+
        ((N : ℝ)*(N-1)*(N-2)*(N-3)*(N-4)/4)*(36*E)+
        (((N : ℝ)*(N-1)*(N-2)*(N-3)*(N-4)*(N-5)/36)*
          (B/(((N-2).choose 3 : ℝ)^2)))*E := by ring
      _ = _ := by rw [hd]; ring
  rw [sumTriples_sq_expanded U h (by omega), ←heq]
  linarith

end KLSBelow25.TripleProjection
#print axioms KLSBelow25.TripleProjection.sumTriples_sq_le_three
#print axioms KLSBelow25.TripleProjection.sumTriples_sq_le_four
#print axioms KLSBelow25.TripleProjection.sumTriples_sq_le_recurrence

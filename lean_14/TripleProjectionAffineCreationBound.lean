import TripleProjectionCreationBound
import TripleCreationBudgetAlgebra

/-! Affine triple-creation estimate retaining the actual diagonal square.
The diagonal is not replaced by its uniform upper bound here. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace KLSBelow25.TripleProjection
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem sumTriples_sq_le_affine_three (U : Triple 3 → H) {Q₃ Q₂ Q₁ Q₀ : ℝ}
    (h : Gram U Q₃ Q₂ Q₁ Q₀) : ‖sumTriples U‖^2≤Q₃ := by
  rw [sumTriples_sq_expanded U h (by norm_num)]
  norm_num

theorem sumTriples_sq_le_affine_four (U : Triple 4 → H) {Q₃ Q₂ Q₁ Q₀ : ℝ}
    (h : Gram U Q₃ Q₂ Q₁ Q₀) (hQ₂ : Q₂≤Q₃) :
    ‖sumTriples U‖^2≤16*Q₃ := by
  rw [sumTriples_sq_expanded U h (by norm_num)]
  norm_num
  linarith

theorem sumTriples_sq_le_affine (U : Triple N → H)
    {Q₃ Q₂ Q₁ Q₀ E B : ℝ} (h : Gram U Q₃ Q₂ Q₁ Q₀) (hN : 5≤N)
    (hQ₂ : Q₂≤Q₃) (hQ₁ : Q₁≤36*E)
    (hQ₀ : Q₀≤(B/(((N-2).choose 3 : ℝ)^2))*E) :
    ‖sumTriples U‖^2 ≤ TripleCreation.affineQ N*Q₃+
      TripleCreation.affineRest B N*E := by
  have hn : (5 : ℝ)≤N := by exact_mod_cast hN
  have h₀ : 0≤(N : ℝ) := Nat.cast_nonneg _
  have h₁ : 0≤(N : ℝ)-1 := by linarith
  have h₂ : 0≤(N : ℝ)-2 := by linarith
  have h₃ : 0≤(N : ℝ)-3 := by linarith
  have h₄ : 0≤(N : ℝ)-4 := by linarith
  have h₅ : 0≤(N : ℝ)-5 := by linarith
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
      ((N : ℝ)*(N-1)*(N-2)/6)*Q₃+
      ((N : ℝ)*(N-1)*(N-2)*(N-3)/2)*Q₃+
      ((N : ℝ)*(N-1)*(N-2)*(N-3)*(N-4)/4)*(36*E)+
      ((N : ℝ)*(N-1)*(N-2)*(N-3)*(N-4)*(N-5)/36)*
        ((B/(((N-2).choose 3 : ℝ)^2))*E) =
      TripleCreation.affineQ N*Q₃+TripleCreation.affineRest B N*E := by
    calc
      _ = ((N : ℝ)*(N-1)*(N-2)/6)*Q₃+
        ((N : ℝ)*(N-1)*(N-2)*(N-3)/2)*Q₃+
        ((N : ℝ)*(N-1)*(N-2)*(N-3)*(N-4)/4)*(36*E)+
        (((N : ℝ)*(N-1)*(N-2)*(N-3)*(N-4)*(N-5)/36)*
          (B/(((N-2).choose 3 : ℝ)^2)))*E := by ring
      _ = _ := by
        rw [hd]
        unfold TripleCreation.affineQ TripleCreation.affineRest
          TripleCreation.chooseThree TripleCreation.recurrenceMultiplier
        ring
  rw [sumTriples_sq_expanded U h (by omega), ←heq]
  linarith

end KLSBelow25.TripleProjection
#print axioms KLSBelow25.TripleProjection.sumTriples_sq_le_affine

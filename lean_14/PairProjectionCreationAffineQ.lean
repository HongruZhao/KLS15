import PairProjectionCreationBound

/-! Creation norm with the exact diagonal pair contraction retained. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace KLSBelow25.PairProjection
set_option maxHeartbeats 1200000
variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem sumPairs_sq_le_affineQ (U : Pair N → H) {Q R S E : ℝ}
    (h : Gram U Q R S) (hN : 3≤N)
    (hR : R≤4*E) (hS : S≤(4+8/(3*((N : ℝ)-2)))*E) :
    ‖sumPairs U‖^2≤((N : ℝ)*((N : ℝ)-1)/2)*Q+
      (N : ℝ)*((N : ℝ)-1)*
        (((N : ℝ)-1)^2+5*((N : ℝ)-1)/3-10/3)*E := by
  have hn : (3 : ℝ)≤N := by exact_mod_cast hN
  have h1 : 0≤(N : ℝ)-1 := by linarith
  have h2 : 0≤(N : ℝ)-2 := by linarith
  have h3 : 0≤(N : ℝ)-3 := by linarith
  have h0 : 0≤(N : ℝ) := Nat.cast_nonneg _
  have hr := mul_le_mul_of_nonneg_left hR (mul_nonneg (mul_nonneg h0 h1) h2)
  have hs := mul_le_mul_of_nonneg_left hS
    (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h0 h1) h2) h3)
      (by norm_num : (0 : ℝ)≤4))
  have he : ((N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2))*(4*E)+
      ((N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2)*((N : ℝ)-3)/4)*
        ((4+8/(3*((N : ℝ)-2)))*E)=
      (N : ℝ)*((N : ℝ)-1)*
        (((N : ℝ)-1)^2+5*((N : ℝ)-1)/3-10/3)*E := by
    have hz : (N : ℝ)-2≠0 := by linarith
    field_simp
    ring
  rw [sumPairs_sq_expanded U h,←he]
  linarith
end KLSBelow25.PairProjection
#print axioms KLSBelow25.PairProjection.sumPairs_sq_le_affineQ

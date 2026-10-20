import PairProjectionHilbert

/-! The closed creation-norm recurrence from genuine one-slot, two-slot,
and previous annihilation bounds. This file is scalar/finite Hilbert algebra. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace KLSBelow25.PairProjection
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem sumPairs_sq_expanded (U : Pair N → H) {Q R S : ℝ} (h : Gram U Q R S) :
    ‖sumPairs U‖^2=
      ((N : ℝ)*((N : ℝ)-1)/2)*Q+
      ((N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2))*R+
      ((N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2)*((N : ℝ)-3)/4)*S := by
  rw [sumPairs_sq U h]
  unfold row
  ring

theorem sumPairs_sq_le_closed (U : Pair N → H) {Q R S E : ℝ}
    (h : Gram U Q R S) (hN : 3≤N)
    (hQ : Q≤8*E) (hR : R≤4*E)
    (hS : S≤(4+8/(3*((N : ℝ)-2)))*E) :
    ‖sumPairs U‖^2≤(N : ℝ)^2*((N : ℝ)-1)*((N : ℝ)-1/3)*E := by
  have hn : (3 : ℝ)≤N := by exact_mod_cast hN
  have h1 : 0≤(N : ℝ)-1 := by linarith
  have h2 : 0≤(N : ℝ)-2 := by linarith
  have h3 : 0≤(N : ℝ)-3 := by linarith
  have h0 : 0≤(N : ℝ) := Nat.cast_nonneg _
  have hq := mul_le_mul_of_nonneg_left hQ
    (div_nonneg (mul_nonneg h0 h1) (by norm_num : (0 : ℝ)≤2))
  have hr := mul_le_mul_of_nonneg_left hR (mul_nonneg (mul_nonneg h0 h1) h2)
  have hs := mul_le_mul_of_nonneg_left hS
    (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h0 h1) h2) h3) (by norm_num : (0 : ℝ)≤4))
  have he : ((N : ℝ)*((N : ℝ)-1)/2)*(8*E)+
      ((N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2))*(4*E)+
      ((N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2)*((N : ℝ)-3)/4)*
        ((4+8/(3*((N : ℝ)-2)))*E)=
      (N : ℝ)^2*((N : ℝ)-1)*((N : ℝ)-1/3)*E := by
    have hz : (N : ℝ)-2≠0 := by linarith
    field_simp
    ring
  rw [sumPairs_sq_expanded U h]
  rw [←he]
  linarith

theorem next_annihilation_cap (hN : 2≤N) :
    ((N : ℝ)^2*((N : ℝ)-1)*((N : ℝ)-1/3))/
      (((N : ℝ)*((N : ℝ)-1)/2)^2)=4+8/(3*((N : ℝ)-1)) := by
  have hn : (2 : ℝ)≤N := by exact_mod_cast hN
  have hz : (N : ℝ)≠0 := by linarith
  have hz1 : (N : ℝ)-1≠0 := by linarith
  field_simp
  ring

theorem cast_choose_three (hN : 2≤N) :
    (N.choose 3 : ℝ)=(N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2)/6 := by
  have hh := congrArg (fun a : ℕ => (a : ℝ)) (Nat.choose_succ_right_eq N 2)
  norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hh
  rw [Nat.cast_choose_two,Nat.cast_sub hN] at hh
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem cast_choose_four (hN : 3≤N) :
    (N.choose 4 : ℝ)=(N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2)*((N : ℝ)-3)/24 := by
  have hh := congrArg (fun a : ℕ => (a : ℝ)) (Nat.choose_succ_right_eq N 3)
  norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hh
  rw [cast_choose_three (by omega),Nat.cast_sub hN] at hh
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem sumPairs_sq_choose (U : Pair N → H) {Q R S : ℝ}
    (h : Gram U Q R S) (hN : 3≤N) :
    ‖sumPairs U‖^2=(N.choose 2 : ℝ)*Q+6*(N.choose 3 : ℝ)*R+6*(N.choose 4 : ℝ)*S := by
  rw [sumPairs_sq_expanded U h,Nat.cast_choose_two,cast_choose_three (by omega),cast_choose_four hN]
  ring

end KLSBelow25.PairProjection
#print axioms KLSBelow25.PairProjection.sumPairs_sq_le_closed
#print axioms KLSBelow25.PairProjection.next_annihilation_cap
#print axioms KLSBelow25.PairProjection.sumPairs_sq_choose

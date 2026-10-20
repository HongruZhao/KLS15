import ScalarBootstrap248764NatCertificate

/-! Scalar original-orbit normalization with a finite restart table. -/
noncomputable section
namespace KLSBelow25
open KLSBelow25Fast

theorem scalar_orbit_bound_of_bootstrap {B K s : ℝ}
    (hB : 0 < B) (hK : 0 < K) (hs : 0 < s)
    (N : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ j ≤ N, 0 < a j) (hb : ∀ j ≤ N, 0 < b j)
    (ha0 : a 0 = 1)
    (hb0 : b 0 ≤ (s^2-K*s-2)/(K*s))
    (hstepa : ∀ j < N, a (j+1) ≤ a j * (1+b j))
    (hstepb : ∀ j < N, b (j+1) ≤ b j-(B/(K^2*s))/a (j+1))
    (hgap : 2*(B/(K^2*s))/a N < (b N)^2)
    (u : ℕ → ℝ) (hseed : u 1 ^ 2-2 ≤ u 2)
    (hrec : ∀ j : ℕ, 0 < u (j+1) → 0 < u (j+2) →
      u (j+2)^2/u (j+1)-B*K^j ≤ u (j+3))
    (henvelope : ∀ rho : ℝ, 1 < rho → ∃ M : ℝ, ∀ j : ℕ,
      u (j+1) ≤ M*(K*rho)^(j+1)) : u 1 ≤ s := by
  by_contra hn
  have hfirst : s < u 1 := not_le.mp hn
  have hu1 : 0 < u 1 := lt_trans hs hfirst
  have hKne := ne_of_gt hK
  have hune := ne_of_gt hu1
  have hsne := ne_of_gt hs
  let epsilon : ℝ := B/(K^2*s)
  let q : ℝ := (s^2-K*s-2)/(K*s)
  let z := normalizedOrbit K u
  have hz0 : z 0 = 1 := by dsimp [z,normalizedOrbit]; simp [hune]
  have hz1 : 1+q < z 1 := by
    have hsq : s^2 < u 1^2 := sq_lt_sq₀ hs.le hu1.le |>.mpr hfirst
    have hnumer : (s^2-2)*(u 1) < (u 1^2-2)*s := by
      have hpos : 0 < (u 1-s)*(s*u 1+2) := by positivity
      nlinarith
    have hdenom : (s^2-2)/(K*s) < (u 1^2-2)/(K*u 1) := by
      apply (div_lt_div_iff₀ (mul_pos hK hs) (mul_pos hK hu1)).mpr
      nlinarith
    have hseed' : (u 1^2-2)/(K*u 1) ≤ z 1 := by
      dsimp [z,normalizedOrbit]
      simpa using (div_le_div_of_nonneg_right hseed (mul_pos hK hu1).le)
    have hidentity : 1+q = (s^2-2)/(K*s) := by
      dsimp [q]
      field_simp <;> ring
    rw [hidentity]
    exact lt_of_lt_of_le hdenom hseed'
  have hnormrec : ∀ j : ℕ, 0 < z j → 0 < z (j+1) →
      z (j+1)^2/z j-epsilon ≤ z (j+2) := by
    intro j hzj hzj1
    have hden : 0 < K^j*u 1 := by positivity
    have hden1 : 0 < K^(j+1)*u 1 := by positivity
    have hden2 : 0 < K^(j+2)*u 1 := by positivity
    have huj : 0 < u (j+1) := (div_pos_iff_of_pos_right hden).mp hzj
    have huj1 : 0 < u (j+2) := by
      have hzj1' : 0 < u (j+2)/(K^(j+1)*u 1) := by
        simpa [z,normalizedOrbit,Nat.add_assoc] using hzj1
      exact (div_pos_iff_of_pos_right hden1).mp hzj1'
    have horig := (div_le_div_of_nonneg_right (hrec j huj huj1) hden2.le)
    have heps : B/(K^2*u 1) ≤ epsilon := by
      dsimp [epsilon]
      exact div_le_div_of_nonneg_left hB.le (by positivity) (by nlinarith [sq_pos_of_pos hK])
    have hidentity :
        (u (j+2)^2/u (j+1)-B*K^j)/(K^(j+2)*u 1) =
          z (j+1)^2/z j-B/(K^2*u 1) := by
      dsimp [z,normalizedOrbit]
      simp only [Nat.add_assoc]
      rw [pow_add K j 2, pow_succ]
      field_simp <;> ring
    have hright : u (j+3)/(K^(j+2)*u 1) = z (j+2) := by
      simp [z,normalizedOrbit,Nat.add_assoc]
    rw [hidentity,hright] at horig
    linarith
  have hnormenv : ∀ rho : ℝ, 1 < rho → ∃ M : ℝ, ∀ j : ℕ, z j ≤ M*rho^j := by
    intro rho hrho
    obtain ⟨M,hM⟩ := henvelope rho hrho
    refine ⟨M*K*rho/u 1,?_⟩
    intro j
    have hbound := div_le_div_of_nonneg_right (hM j) (show 0 ≤ K^j*u 1 by positivity)
    have heq : M*(K*rho)^(j+1)/(K^j*u 1) = (M*K*rho/u 1)*rho^j := by
      rw [mul_pow,pow_succ,pow_succ]
      field_simp <;> ring
    rw [heq] at hbound
    exact hbound
  have hinit : 1+b 0 ≤ z 1 := by
    have := hb0
    change b 0 ≤ q at this
    linarith
  exact scalar_finite_bootstrap_impossible (by positivity)
    N a b ha hb ha0 hstepa hstepb hgap z hz0 hinit hnormrec hnormenv

theorem scalar_orbit_bound_248764
    (u : ℕ → ℝ) (hseed : u 1^2-2 ≤ u 2)
    (hrec : ∀ j : ℕ, 0 < u (j+1) → 0 < u (j+2) →
      u (j+2)^2/u (j+1)-(121/4)*(2221/100)^j ≤ u (j+3))
    (henvelope : ∀ rho : ℝ, 1 < rho → ∃ M : ℝ, ∀ j : ℕ,
      u (j+1) ≤ M*((2221/100)*rho)^(j+1)) : u 1 ≤ 59691/2500 := by
  exact scalar_orbit_bound_of_bootstrap (B:=121/4) (K:=2221/100) (s:=59691/2500)
    (by norm_num) (by norm_num) (by norm_num) 200
    bootstrap248764A bootstrap248764B
    bootstrap248764_a_positive bootstrap248764_b_positive bootstrap248764_a_initial
    bootstrap248764_b_initial bootstrap248764_a_step bootstrap248764_b_step
    bootstrap248764_final_gap u hseed hrec henvelope

#print axioms scalar_orbit_bound_of_bootstrap
#print axioms scalar_orbit_bound_248764
end KLSBelow25

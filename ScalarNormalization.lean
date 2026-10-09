import ScalarSpectralContradiction

/-! Proposition 7.3's scalar normalization and contradiction.  The original
orbit recurrence and every-rate envelope remain explicit hypotheses; no
operator, Appell, or actual-law assertion is introduced here. -/
noncomputable section
namespace KLSBelow25

def normalizedOrbit (K : ℝ) (u : ℕ → ℝ) (j : ℕ) : ℝ :=
  u (j+1)/(K^j*u 1)

theorem scalar_orbit_bound {B K s : ℝ} (hB : 0 < B) (hK : 0 < K) (hs : 0 < s)
    (hDelta : 0 < s^2-K*s-2) (hGap : 2*B*s < (s^2-K*s-2)^2)
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
  have he : 0 < epsilon := by dsimp [epsilon]; positivity
  have hq : 0 < q := div_pos hDelta (mul_pos hK hs)
  have hgap : 2*epsilon < q^2 := by
    calc
      2*epsilon = (2*B*s)/(K*s)^2 := by
        dsimp [epsilon]
        field_simp <;> ring
      _ < (s^2-K*s-2)^2/(K*s)^2 :=
        div_lt_div_of_pos_right hGap (by positivity)
      _ = q^2 := by dsimp [q]; ring
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
  have hcontra := scalar_initial_gap_impossible he hq hgap z hz0 hnormrec hnormenv
  exact (not_lt_of_ge hcontra) hz1

theorem scalar_orbit_bound_25
    (u : ℕ → ℝ) (hseed : u 1^2-2 ≤ u 2)
    (hrec : ∀ j : ℕ, 0 < u (j+1) → 0 < u (j+2) →
      u (j+2)^2/u (j+1)-(121/4)*(223/10)^j ≤ u (j+3))
    (henvelope : ∀ rho : ℝ, 1 < rho → ∃ M : ℝ, ∀ j : ℕ,
      u (j+1) ≤ M*((223/10)*rho)^(j+1)) : u 1 ≤ 24 := by
  exact scalar_orbit_bound (B:=121/4) (K:=223/10) (s:=24)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    u hseed hrec henvelope

theorem scalar_orbit_bound_24886
    (u : ℕ → ℝ) (hseed : u 1^2-2 ≤ u 2)
    (hrec : ∀ j : ℕ, 0 < u (j+1) → 0 < u (j+2) →
      u (j+2)^2/u (j+1)-(121/4)*(2221/100)^j ≤ u (j+3))
    (henvelope : ∀ rho : ℝ, 1 < rho → ∃ M : ℝ, ∀ j : ℕ,
      u (j+1) ≤ M*((2221/100)*rho)^(j+1)) : u 1 ≤ 11943/500 := by
  exact scalar_orbit_bound (B:=121/4) (K:=2221/100) (s:=11943/500)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    u hseed hrec henvelope

#print axioms scalar_orbit_bound
#print axioms scalar_orbit_bound_25
#print axioms scalar_orbit_bound_24886
end KLSBelow25

import Quintic24886

noncomputable section
namespace Quintic24886

theorem hasDerivAt_W (v : ℝ) : HasDerivAt W (Wp v) v := by
  have h := (((((hasDerivAt_const v (1 : ℝ)).sub
    ((hasDerivAt_id' v).const_mul (16 / 5))).add
    (((hasDerivAt_id' v).pow 2).const_mul (88 / 25))).sub
    (((hasDerivAt_id' v).pow 3).const_mul (176 / 125))).add
    (((hasDerivAt_id' v).pow 4).const_mul (44 / 625))).add
    (((hasDerivAt_id' v).pow 5).const_mul kappa)
  convert h using 1 <;> first | rfl | (ext t; norm_num [W, Wp] <;> ring) | (norm_num [W, Wp] <;> ring)

theorem hasDerivAt_Wp (v : ℝ) : HasDerivAt Wp (Wpp v) v := by
  have h := (((((hasDerivAt_const v (-16 / 5 : ℝ)).add
    ((hasDerivAt_id' v).const_mul (176 / 25))).sub
    (((hasDerivAt_id' v).pow 2).const_mul (528 / 125))).add
    (((hasDerivAt_id' v).pow 3).const_mul (176 / 625))).add
    (((hasDerivAt_id' v).pow 4).const_mul (5 * kappa)))
  convert h using 1 <;> first | rfl | (ext t; norm_num [Wp, Wpp] <;> ring) | (norm_num [Wp, Wpp] <;> ring)

theorem hasDerivAt_x (z : ℝ) : HasDerivAt x (-L) z := by
  convert ((hasDerivAt_const z (1 : ℝ)).sub (hasDerivAt_id' z)).const_mul L using 1 <;>
    first | rfl | (simp [x] <;> ring)

theorem hasDerivAt_U (z : ℝ) : HasDerivAt U (Up z) z := by
  have h₁ := ((hasDerivAt_id' z).const_mul P).add_const Q
  have h₂ := ((hasDerivAt_W (x z)).comp z (hasDerivAt_x z)).const_mul (P + Q)
  convert h₁.sub h₂ using 1 <;> first | rfl | (ext t; norm_num [U, Up] <;> ring) | (norm_num [U, Up] <;> ring)

theorem hasDerivAt_Up (z : ℝ) : HasDerivAt Up (Upp z) z := by
  have h := ((hasDerivAt_Wp (x z)).comp z (hasDerivAt_x z)).const_mul ((P + Q) * L)
  convert (hasDerivAt_const z P).add h using 1 <;> first | rfl | (ext t; norm_num [Up, Upp] <;> ring) | (norm_num [Up, Upp] <;> ring)

theorem Upp_negative_on_interval {z : ℝ} (hz : z ∈ Set.Icc (29 / 50) 1) :
    Upp z < 0 := by
  have hx := x_range hz
  have hp := Wpp_positive hx.1 hx.2
  norm_num [Upp, P, Q, L]
  nlinarith

theorem Up_strictAntiOn : StrictAntiOn Up (Set.Icc (29 / 50) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact (continuous_iff_continuousAt.mpr
      (fun z => (hasDerivAt_Up z).continuousAt)).continuousOn
  · intro z hz
    rw [(hasDerivAt_Up z).deriv]
    exact Upp_negative_on_interval (interior_subset hz)

theorem Up_negative_on_interval {z : ℝ} (hz : z ∈ Set.Icc (29 / 50) 1) :
    Up z < 0 := by
  have h := Up_strictAntiOn.antitoneOn
    (show (29 / 50 : ℝ) ∈ Set.Icc (29 / 50) 1 by norm_num) hz hz.1
  exact lt_of_le_of_lt h barrier_endpoint_derivative_negative

theorem U_strictAntiOn : StrictAntiOn U (Set.Icc (29 / 50) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact (continuous_iff_continuousAt.mpr
      (fun z => (hasDerivAt_U z).continuousAt)).continuousOn
  · intro z hz
    rw [(hasDerivAt_U z).deriv]
    exact Up_negative_on_interval (interior_subset hz)

theorem U_nonnegative_on_interval {z : ℝ} (hz : z ∈ Set.Icc (29 / 50) 1) :
    0 ≤ U z := by
  have h := U_strictAntiOn.antitoneOn hz
    (show (1 : ℝ) ∈ Set.Icc (29 / 50) 1 by norm_num) hz.2
  rw [barrier_at_one] at h
  exact h

theorem U_branch_has_all_values (u : ℝ) (hu : u ∈ Set.Icc 0 1) :
    ∃! z, z ∈ Set.Icc (29 / 50) 1 ∧ U z = u := by
  have hcont : ContinuousOn U (Set.Icc (29 / 50) 1) :=
    (continuous_iff_continuousAt.mpr (fun z => (hasDerivAt_U z).continuousAt)).continuousOn
  have hlo : U 1 ≤ u := by rw [barrier_at_one]; exact hu.1
  have hhi : u ≤ U (29 / 50) := le_trans hu.2 (le_of_lt barrier_endpoint_above_one)
  obtain ⟨z, hz, hzu⟩ := intermediate_value_Icc' (by norm_num : (29 / 50 : ℝ) ≤ 1)
    hcont ⟨hlo, hhi⟩
  refine ⟨z, ⟨hz, hzu⟩, ?_⟩
  intro y hy
  apply U_strictAntiOn.injOn hy.1 hz
  exact hy.2.trans hzu.symm

theorem sqrt_le_tangent_nine_tenths {v : ℝ} (hv : 0 ≤ v) :
    Real.sqrt v ≤ 5 * v / 9 + 9 / 20 := by
  have hs := Real.sq_sqrt hv
  nlinarith [sq_nonneg (Real.sqrt v - 9 / 10)]

theorem strict_barrier_margin {z : ℝ} (hz : z ∈ Set.Icc (29 / 50) 1) :
    0 < alpha * K * z - A * U z - r * Real.sqrt (U z) +
      (2 * z + r * Real.sqrt z) * Up z := by
  have hu := U_nonnegative_on_interval hz
  have hup := Up_negative_on_interval hz
  obtain ⟨hr, hrR, _⟩ := parameter_ranges
  have hR : 0 ≤ R := by norm_num [R]
  have hRu : r * Real.sqrt (U z) < cu * U z + b := by
    have h1 := mul_le_mul_of_nonneg_left (sqrt_le_tangent_nine_tenths hu) hr.le
    have h2 := mul_lt_mul_of_pos_right hrR
      (show 0 < 5 * U z / 9 + 9 / 20 by linarith)
    calc
      r * Real.sqrt (U z) ≤ r * (5 * U z / 9 + 9 / 20) := h1
      _ < R * (5 * U z / 9 + 9 / 20) := h2
      _ = cu * U z + b := by rw [coefficient_cu, coefficient_b]; ring
  have hRz : r * Real.sqrt z ≤ 5 * R / 9 * z + 9 * R / 20 := by
    have hz0 : 0 ≤ z := le_trans (by norm_num : (0 : ℝ) ≤ 29 / 50) hz.1
    have h1 := mul_le_mul_of_nonneg_right hrR.le (Real.sqrt_nonneg z)
    have h2 := mul_le_mul_of_nonneg_left (sqrt_le_tangent_nine_tenths hz0) hR
    calc
      r * Real.sqrt z ≤ R * Real.sqrt z := h1
      _ ≤ R * (5 * z / 9 + 9 / 20) := h2
      _ = 5 * R / 9 * z + 9 * R / 20 := by ring
  have hcoeff : 2 * z + r * Real.sqrt z ≤ a * z + b := by
    rw [coefficient_a, coefficient_b]
    nlinarith
  have hproduct := mul_le_mul_of_nonpos_right hcoeff hup.le
  have hres := barrier_residual_nonnegative hz
  have hc := coefficient_c
  nlinarith

theorem finite_degree_correction_positive {v rho sigma t : ℝ}
    (hv : 0 ≤ v) (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma)
    (ht : 0 < t) (htop : t ≤ 1 / 4) :
    0 < t * (1 + (A + 3) * v + (1 - 2 * delta) * rho +
      (3 - 2 * delta) * sigma) +
      t ^ 2 * (-5 * v + (2 - 2 * delta) * rho - 2) := by
  let bc := 1 + (A + 3) * v + (1 - 2 * delta) * rho + (3 - 2 * delta) * sigma
  let dc := -5 * v + (2 - 2 * delta) * rho - 2
  have hb : 0 < bc := by dsimp [bc]; norm_num [A, delta]; positivity
  have hend : 0 < bc + dc / 4 := by
    have he : bc + dc / 4 = 1 / 2 + (A + 7 / 4) * v +
        (3 / 2 - 5 * delta / 2) * rho + (3 - 2 * delta) * sigma := by
      dsimp [bc, dc]; ring
    rw [he]
    norm_num [A, delta]
    positivity
  have hp := KLSBelow25.affine_positive_of_endpoint hb hend ht.le htop
  have hm := mul_pos ht hp
  dsimp [bc, dc] at hm
  nlinarith

#print axioms hasDerivAt_U
#print axioms U_branch_has_all_values
#print axioms strict_barrier_margin
#print axioms finite_degree_correction_positive
end Quintic24886

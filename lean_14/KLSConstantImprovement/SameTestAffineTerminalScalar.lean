import KLSConstantImprovement.ActualSameTestAffineCovariance

/-! Pay the same terminal coordinate charge while lowering the constant in
the creation ratio. The energy range is explicit and can be supplied by the
accepted raw cubic cap and a candidate barrier's positive lower threshold. -/
noncomputable section
namespace KLSConstantImprovement.SameTestAffineTerminalScalar
set_option maxHeartbeats 5000000

def radical (c X Y : ℝ) : ℝ := (4*c-Y)*Y*(72*c/X-1)/c^2
def linearB (X Y : ℝ) : ℝ := 4*Y+72*Y^2/X
def doubleRatio (c X Y : ℝ) : ℝ := Y/c+Real.sqrt (radical c X Y)

theorem radical_lower_square {c X Y : ℝ}
    (hc : 13 ≤ c) (hX0 : 360 ≤ X) (hX1 : X ≤ 859)
    (hY0 : 0 ≤ Y) (hY1 : Y ≤ 8) :
    (Y/(3*c))^2 ≤ radical c X Y := by
  have hcp : 0 < c := by linarith
  have hXp : 0 < X := by linarith
  have ha : 44 ≤ 4*c-Y := by linarith
  have hb : 77 ≤ 72*c-X := by linarith
  have hab : (3388 : ℝ) ≤ (4*c-Y)*(72*c-X) := by
    calc
      _ = (44 : ℝ)*77 := by norm_num
      _ ≤ (4*c-Y)*(72*c-X) := mul_le_mul ha hb (by norm_num) (by linarith)
  have hid : (4*c-Y)*(72*c/X-1) = ((4*c-Y)*(72*c-X))/X := by
    field_simp [hXp.ne']
    <;> ring
  have hfactor : 1 ≤ (4*c-Y)*(72*c/X-1) := by
    rw [hid]
    apply (le_div_iff₀ hXp).mpr
    nlinarith [hab]
  have hm := mul_le_mul_of_nonneg_right hfactor hY0
  have hn : Y ≤ (4*c-Y)*Y*(72*c/X-1) := by nlinarith [hm]
  have hsq : 0 < c^2 := sq_pos_of_pos hcp
  calc
    (Y/(3*c))^2 = (Y^2/9)/c^2 := by field_simp [hcp.ne']; ring
    _ ≤ Y/c^2 := (div_le_div_iff_of_pos_right hsq).mpr (by nlinarith)
    _ ≤ radical c X Y := (div_le_div_iff_of_pos_right hsq).mpr hn

theorem linearB_upper {X Y : ℝ} (hX : 360 ≤ X)
    (hY0 : 0 ≤ Y) (hY1 : Y ≤ 8) : linearB X Y ≤ 28*Y/5 := by
  have hXp : 0 < X := by linarith
  have h1 : 72*Y ≤ (8/5 : ℝ)*X := by linarith
  have h2 := mul_le_mul_of_nonneg_right h1 hY0
  have h3 : 72*Y^2 ≤ (8*Y/5)*X := by nlinarith [h2]
  have h4 := (div_le_iff₀ hXp).mpr h3
  unfold linearB
  linarith

theorem radical_difference {c c0 X Y : ℝ}
    (hc : c ≠ 0) (hc0 : c0 ≠ 0) (hX : X ≠ 0) :
    radical c X Y-radical c0 X Y =
      (c-c0)*linearB X Y/(c*c0)-Y^2*(c-c0)*(c+c0)/(c^2*c0^2) := by
  unfold radical linearB
  field_simp [hc, hc0, hX]
  <;> ring

theorem radical_root_increment {c c0 X Y : ℝ}
    (hc0 : 13 ≤ c0) (hc : c0 ≤ c)
    (hX0 : 360 ≤ X) (hX1 : X ≤ 859) (hY0 : 0 ≤ Y) (hY1 : Y ≤ 8) :
    Real.sqrt (radical c X Y) ≤ Real.sqrt (radical c0 X Y)+(c-c0) := by
  have hcp : 0 < c := by linarith
  have hc0p : 0 < c0 := by linarith
  have hXp : 0 < X := by linarith
  have hd : 0 ≤ c-c0 := sub_nonneg.mpr hc
  have hfloor := radical_lower_square hc0 hX0 hX1 hY0 hY1
  have hr0 : 0 ≤ radical c0 X Y := (sq_nonneg _).trans hfloor
  have hs0 : Y/(3*c0) ≤ Real.sqrt (radical c0 X Y) := by
    have hh := Real.abs_le_sqrt hfloor
    rwa [abs_of_nonneg (div_nonneg hY0 (by positivity))] at hh
  have hB : linearB X Y/(c*c0) ≤ 2*Y/(3*c0) := by
    apply (div_le_iff₀ (mul_pos hcp hc0p)).mpr
    calc
      linearB X Y ≤ 28*Y/5 := linearB_upper hX0 hY0 hY1
      _ ≤ (2/3 : ℝ)*c*Y := by
        have hh : (28/5 : ℝ) ≤ (2/3 : ℝ)*c := by linarith
        nlinarith [mul_le_mul_of_nonneg_right hh hY0]
      _ = (2*Y/(3*c0))*(c*c0) := by field_simp [hc0p.ne'] <;> ring
  have hdiff : radical c X Y-radical c0 X Y ≤
      (c-c0)*(linearB X Y/(c*c0)) := by
    rw [radical_difference hcp.ne' hc0p.ne' hXp.ne']
    have ht : 0 ≤ Y^2*(c-c0)*(c+c0)/(c^2*c0^2) := by positivity
    calc
      _ ≤ (c-c0)*linearB X Y/(c*c0) := sub_le_self _ ht
      _ = _ := by ring
  have hb := mul_le_mul_of_nonneg_left hB hd
  have hs := mul_le_mul_of_nonneg_left hs0 (by linarith : 0 ≤ 2*(c-c0))
  have hstep : radical c X Y ≤ radical c0 X Y+
      2*(c-c0)*Real.sqrt (radical c0 X Y) := by
    calc
      _ ≤ radical c0 X Y+(c-c0)*(linearB X Y/(c*c0)) := by linarith [hdiff]
      _ ≤ radical c0 X Y+(c-c0)*(2*Y/(3*c0)) := add_le_add (le_refl _) hb
      _ = radical c0 X Y+2*(c-c0)*(Y/(3*c0)) := by ring
      _ ≤ _ := add_le_add (le_refl _) hs
  have hsq : radical c X Y ≤ (Real.sqrt (radical c0 X Y)+(c-c0))^2 := by
    nlinarith [Real.sq_sqrt hr0, sq_nonneg (c-c0)]
  have hroot := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) hd)] at hroot

theorem doubleRatio_increment {c c0 X Y : ℝ}
    (hc0 : 13 ≤ c0) (hc : c0 ≤ c)
    (hX0 : 360 ≤ X) (hX1 : X ≤ 859) (hY0 : 0 ≤ Y) (hY1 : Y ≤ 8) :
    doubleRatio c X Y ≤ doubleRatio c0 X Y+(c-c0) := by
  have hcp : 0 < c := by linarith
  have hc0p : 0 < c0 := by linarith
  have hy : Y/c ≤ Y/c0 :=
    (div_le_div_iff₀ hcp hc0p).mpr (mul_le_mul_of_nonneg_left hc hY0)
  have hr := radical_root_increment hc0 hc hX0 hX1 hY0 hY1
  unfold doubleRatio
  linarith

theorem same_terminal_coordinate_compensation {C r X Y lam : ℝ}
    (hC : 14 ≤ C) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hX0 : 360 ≤ X) (hX1 : X ≤ 859) (hY0 : 0 ≤ Y) (hY1 : Y ≤ 8)
    (hlam : X ≤ lam) :
    lam*r+X*doubleRatio (C-r) X Y ≤ lam+X*doubleRatio (C-1) X Y := by
  have hr := doubleRatio_increment (by linarith : 13 ≤ C-1)
    (by linarith : C-1 ≤ C-r) hX0 hX1 hY0 hY1
  have hm := mul_le_mul_of_nonneg_left hr (by linarith : 0 ≤ X)
  have hs := mul_nonneg (sub_nonneg.mpr hlam) (sub_nonneg.mpr hr1)
  nlinarith [hm, hs]

end KLSConstantImprovement.SameTestAffineTerminalScalar
#print axioms KLSConstantImprovement.SameTestAffineTerminalScalar.radical_lower_square
#print axioms KLSConstantImprovement.SameTestAffineTerminalScalar.linearB_upper
#print axioms KLSConstantImprovement.SameTestAffineTerminalScalar.radical_difference
#print axioms KLSConstantImprovement.SameTestAffineTerminalScalar.radical_root_increment
#print axioms KLSConstantImprovement.SameTestAffineTerminalScalar.doubleRatio_increment
#print axioms KLSConstantImprovement.SameTestAffineTerminalScalar.same_terminal_coordinate_compensation

import CreationSeed239Inverse

/-! A parameter cap for the genuine descending cubic seed.  This includes
the closed parameter endpoints and never extrapolates its inverse branch. -/
noncomputable section
open Set
namespace KLSBelow25.CreationSeed239

theorem seed_argument_le_parameter_value {t x : ℝ}
    (ht : t ∈ Icc (0 : ℝ) seedT) (hx : x ∈ Icc (0 : ℝ) 1)
    (hcurve : 1-t^2 ≤ seedPhi x) :
    x ≤ t^2*(seedV t)^2 := by
  let z : ℝ := 1-t^2
  have hzleft : seedInverseBarrier.left ≤ z := by
    change 1-seedT^2 ≤ 1-t^2
    nlinarith [ht.1,ht.2,seedT_range.1]
  have hzupper : z ≤ 1 := by dsimp [z]; nlinarith [sq_nonneg t]
  have hvalue : seedInverseBarrier.U z = t^2*(seedV t)^2 := by
    change RadicalBarrier.value seedV (1-t^2) = _
    simp only [RadicalBarrier.value, RadicalBarrier.parameter, sub_sub_cancel,
      Real.sqrt_sq ht.1]
  rw [← hvalue]
  by_cases he : z = seedInverseBarrier.left
  · rw [he]
    exact hx.2.trans seedInverseBarrier.endpoint.le
  · have hzbranch : z ∈ seedInverseBarrier.branch :=
      ⟨lt_of_le_of_ne hzleft (Ne.symm he),
        hzupper.trans_lt seedInverseBarrier.one_lt_right⟩
    have hc := seedInverseBarrier.strictAntiOn_U.antitoneOn hzbranch
      (seedInverseBarrier.phi_open_branch hx) hcurve
    rw [(seedInverseBarrier.phi_branch_of_unit hx).2] at hc
    exact hc

theorem quadratic_energy_le_parameter_cap {t u Z : ℝ}
    (ht : t ∈ Icc (0 : ℝ) seedT) (_hu : u ∈ Icc (0 : ℝ) 1)
    (hZ : Z ∈ Icc (0 : ℝ) 8) (hseed : u ≤ seedPhi (Z/8))
    (hparameter : 1-t^2 ≤ u) :
    Z ≤ 8*t^2*(seedV t)^2 := by
  have hx : Z/8 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hZ.1,hZ.2]
  have hc := seed_argument_le_parameter_value ht hx (hparameter.trans hseed)
  nlinarith

end KLSBelow25.CreationSeed239

#print axioms KLSBelow25.CreationSeed239.seed_argument_le_parameter_value
#print axioms KLSBelow25.CreationSeed239.quadratic_energy_le_parameter_cap

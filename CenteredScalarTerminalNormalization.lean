import ActualCenteredAdjacentMaximum
import ActualScalarTerminalNormalization

/-! Exact normalization of the terminal weighted energy inequality. The
square-root factors are retained with their true positive denominators. -/
noncomputable section
namespace KLS.DeterministicBridgeNext
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 theorem centered_weighted_terminal_normalization {hk X Y u q α A k j dk dj : ℝ}
    (hhk : 0 < hk) (hX : 0 < X) (hY : Y = hk*u) :
    X*(q*(α*X/hk-(A*k^2+(A-3)*k+1)*u-2*dk/Real.sqrt hk*Real.sqrt u)-
      (2*j^2-j+1)-2*dj/Real.sqrt X) =
      (X*q/hk)*α*X-(2*j^2-j)*X-(X*q/hk)*(A*k^2+(A-3)*k)*Y-
      X*(1+u*q)-2*Real.sqrt X*dj-2*(X*q/hk)*Real.sqrt Y*dk := by
  have hhkne := hhk.ne'
  have hshk := (Real.sqrt_pos.mpr hhk).ne'
  have hsX := (Real.sqrt_pos.mpr hX).ne'
  have hydiv : Real.sqrt Y/hk = Real.sqrt u/Real.sqrt hk := by
    rw [hY,Real.sqrt_mul hhk.le]
    apply (div_eq_div_iff hhkne hshk).mpr
    have hh := Real.mul_self_sqrt hhk.le
    calc
      Real.sqrt hk*Real.sqrt u*Real.sqrt hk = (Real.sqrt hk*Real.sqrt hk)*Real.sqrt u := by ring
      _ = hk*Real.sqrt u := by rw [hh]
      _ = Real.sqrt u*hk := by ring
  have hxdiv : X/Real.sqrt X = Real.sqrt X := by
    apply (div_eq_iff hsX).mpr
    exact (Real.mul_self_sqrt hX.le).symm
  calc
    _ = X*q*(α*X/hk-(A*k^2+(A-3)*k+1)*u)-
        2*X*q*dk*(Real.sqrt Y/hk)-X*(2*j^2-j+1)-2*dj*(X/Real.sqrt X) := by
      rw [hydiv]
      ring
    _ = _ := by
      rw [hxdiv,hY]
      field_simp [hhkne]
      ring

 theorem centered_normalized_terminal_nonpos {hk X Y u q α A k j dk dj : ℝ}
    (hhk : 0 < hk) (hX : 0 < X) (hY : Y = hk*u)
    (hterminal : (X*q/hk)*α*X-(2*j^2-j)*X-(X*q/hk)*(A*k^2+(A-3)*k)*Y-
      X*(1+u*q)-2*Real.sqrt X*dj-2*(X*q/hk)*Real.sqrt Y*dk ≤ 0) :
    q*(α*X/hk-(A*k^2+(A-3)*k+1)*u-2*dk/Real.sqrt hk*Real.sqrt u)-
      (2*j^2-j+1)-2*dj/Real.sqrt X ≤ 0 := by
  have he := centered_weighted_terminal_normalization (q := q) (α := α) (A := A)
    (k := k) (j := j) (dk := dk) (dj := dj) hhk hX hY
  rw [← he] at hterminal
  exact nonpos_of_mul_nonpos_right hterminal hX

 theorem centered_weighted_terminal_excess_contradiction
    {hk hj X Y u q α A k j dk dj v : ℝ}
    (hhk : 0 < hk) (hhj : 0 < hj) (hv : 0 < v) (hα : 0 < α)
    (hq : 0 < q) (hdj : 0 ≤ dj) (hX : hj*v < X) (hY : Y = hk*u)
    (hcriterion : q*(α*hj/hk*v-(A*k^2+(A-3)*k+1)*u-
      2*dk/Real.sqrt hk*Real.sqrt u) >
      (2*j^2-j+1)+2*dj/Real.sqrt (hj*v))
    (hterminal : (X*q/hk)*α*X-(2*j^2-j)*X-(X*q/hk)*(A*k^2+(A-3)*k)*Y-
      X*(1+u*q)-2*Real.sqrt X*dj-2*(X*q/hk)*Real.sqrt Y*dk ≤ 0) : False := by
  have hXp : 0 < X := (mul_pos hhj hv).trans hX
  exact scalar_coefficient_excess_contradiction hα hhk hhj hv hq hdj hX hcriterion
    (centered_normalized_terminal_nonpos hhk hXp hY hterminal)

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.centered_weighted_terminal_normalization
#print axioms KLS.DeterministicBridgeNext.centered_weighted_terminal_excess_contradiction

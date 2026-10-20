import CenteredScalarTerminalNormalization

/-! The exact scalar criterion for the improved adjacent cubic/quartic
display. The lower second energy remains an independent actual variable. -/
noncomputable section
namespace KLS.DeterministicBridgeNext
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem quartic_creation_terminal_excess_contradiction
    {H J X Y Z u q α z : ℝ} (hH : 0 < H) (hJ : 0 < J) (hz : 0 < z)
    (hα : 0 < α) (hq : 0 < q) (hX : J*z < X) (hY : Y=H*u)
    (hcriterion :
      q*(α*J/H*z-(44/(1-α)-32)*u-2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u) >
        29+2*(Real.sqrt (176*H*u)+Real.sqrt (13824*Z))/Real.sqrt (J*z))
    (hterminal :
      (X*q/H)*α*X-28*X-(X*q/H)*(44/(1-α)-33)*Y-X*(1+u*q)-
        2*Real.sqrt X*(Real.sqrt (176*Y)+Real.sqrt (13824*Z))-
        2*(X*q/H)*Real.sqrt Y*Real.sqrt (48*Z) ≤ 0) : False := by
  let A : ℝ := (44/(1-α)-24)/12
  have hloss : A*3^2+(A-3)*3=44/(1-α)-33 := by dsimp [A]; ring
  have hloss' : A*3^2+(A-3)*3+1=44/(1-α)-32 := by rw [hloss]; ring
  have hc : q*(α*J/H*z-(A*3^2+(A-3)*3+1)*u-
      2*Real.sqrt (48*Z)/Real.sqrt H*Real.sqrt u) >
      (2*4^2-4+1)+2*(Real.sqrt (176*Y)+Real.sqrt (13824*Z))/Real.sqrt (J*z) := by
    rw [hloss',hY]
    simpa only [show (2:ℝ)*4^2-4+1=29 by norm_num,mul_assoc] using hcriterion
  have ht : (X*q/H)*α*X-(2*4^2-4)*X-(X*q/H)*(A*3^2+(A-3)*3)*Y-
      X*(1+u*q)-2*Real.sqrt X*(Real.sqrt (176*Y)+Real.sqrt (13824*Z))-
      2*(X*q/H)*Real.sqrt Y*Real.sqrt (48*Z) ≤ 0 := by
    rw [hloss]
    simpa only [show (2:ℝ)*4^2-4=28 by norm_num] using hterminal
  exact centered_weighted_terminal_excess_contradiction hH hJ hz hα hq
    (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hX hY hc ht

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.quartic_creation_terminal_excess_contradiction

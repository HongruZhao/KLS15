import KLSConstantImprovement.FullSymmetricProductionCoercivity

/-! Exact same-field loss accounting after full3 coercivity.
The actual norm/source/graph identifications remain explicit. The numerical
reduced-payment premise in the last declaration is OPEN, not asserted here. -/
namespace KLSConstantImprovement.FullSymmetricProductionExactLoss

theorem exact_full_symmetric_error
    (W col row a h ht c E dSym : ℝ)
    (hc : col = a + h)
    (horder : 2 * (col - row) = 3 * (h - ht))
    (hE : E = 4 * W + a + h - 4 * c)
    (hd : dSym = a - 4 * c / 3 + 4 * W / 9) :
    E = 8 * W / 3 - 2 * row + 3 * ht + 3 * dSym := by
  linarith

theorem exact_full_rate_production
    (W row ht E dSym PFcol center Xi : ℝ)
    (hE : E = 8 * W / 3 - 2 * row + 3 * ht + 3 * dSym)
    (hXi : Xi = PFcol + E / 2 + 8 * center) :
    Xi = PFcol + 4 * W / 3 - row + 3 * ht / 2
      + 8 * center + 3 * dSym / 2 := by
  linarith

theorem exact_actual_response_loss
    (W r cf row theta extra PFcol PFrow ht center dSym Xi MF Lprod : ℝ)
    (hXi : Xi = PFcol + 4 * W / 3 - row + 3 * ht / 2
      + 8 * center + 3 * dSym / 2)
    (hrow : theta = row + PFrow)
    (hcurvature : theta + extra = 2 * r - 2 * cf)
    (hMF : MF = W + r - cf - (Xi + extra) / 2)
    (hL : Lprod = extra + (PFcol + PFrow) / 2 + 3 * ht / 4
      + 4 * center + 3 * dSym / 4) :
    MF = W / 3 + 2 * (r - cf) - Lprod := by
  linarith

theorem reduced_response_payment
    (I MF W r cf Lprod responseLoss mainDefect allowance : ℝ)
    (hMF : MF = W / 3 + 2 * (r - cf) - Lprod)
    (hI : I = MF - responseLoss)
    (hpayment : W / 3 - 2 * cf - allowance ≤
      Lprod + responseLoss + 4 * mainDefect / 7) :
    I - 4 * mainDefect / 7 ≤ 2 * r + allowance := by
  linarith

end KLSConstantImprovement.FullSymmetricProductionExactLoss
#print axioms KLSConstantImprovement.FullSymmetricProductionExactLoss.exact_full_symmetric_error
#print axioms KLSConstantImprovement.FullSymmetricProductionExactLoss.exact_full_rate_production
#print axioms KLSConstantImprovement.FullSymmetricProductionExactLoss.exact_actual_response_loss
#print axioms KLSConstantImprovement.FullSymmetricProductionExactLoss.reduced_response_payment

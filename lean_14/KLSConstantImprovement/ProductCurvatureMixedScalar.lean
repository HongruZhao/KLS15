import KLSConstantImprovement.DeficitCurvatureScalar

/-! Exact mixed-pair scalar SOS underlying product closure of integrated
cubic curvature. Factor cumulant identification and indexing are separate;
all actual factor deficit/Bessel inputs remain explicit in this algebra. -/
noncomputable section
namespace KLSConstantImprovement.ProductCurvatureMixedScalar

def pairForm (k U V FU FV Z : ℝ) : ℝ :=
  (12-k)*(FU+FV)+18*k*(U+V)+24*Z

theorem pairForm_sos (k U V FU FV AU AV Z : ℝ) :
    pairForm k U V FU FV Z=
      k*((6*U-FU)+(6*V-FV))+12*(k-2)*(U+V)+
      12*((FU+2*U-AU)+(FV+2*V-AV))+12*(AU+AV+2*Z) := by
  unfold pairForm
  ring

theorem pairForm_nonnegative {k U V FU FV AU AV Z : ℝ} (hk : 2≤k)
    (hU : 0≤U) (hV : 0≤V) (hFU : FU≤6*U) (hFV : FV≤6*V)
    (hBU : AU≤FU+2*U) (hBV : AV≤FV+2*V) (hGram : 0≤AU+AV+2*Z) :
    0≤pairForm k U V FU FV Z := by
  rw [pairForm_sos k U V FU FV AU AV Z]
  have hk0:0≤k := by linarith
  have hk2:0≤k-2 := by linarith
  exact add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg hk0 (add_nonneg (sub_nonneg.mpr hFU) (sub_nonneg.mpr hFV)))
    (mul_nonneg (mul_nonneg (by norm_num) hk2) (add_nonneg hU hV)))
    (mul_nonneg (by norm_num) (add_nonneg (sub_nonneg.mpr hBU) (sub_nonneg.mpr hBV))))
    (mul_nonneg (by norm_num) hGram)

theorem three_factor_charge_nonnegative {k N : ℝ} (hk : 2≤k) (hN : 0≤N) :
    0≤36*k*N := mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hN

end KLSConstantImprovement.ProductCurvatureMixedScalar
#print axioms KLSConstantImprovement.ProductCurvatureMixedScalar.pairForm_sos
#print axioms KLSConstantImprovement.ProductCurvatureMixedScalar.pairForm_nonnegative
#print axioms KLSConstantImprovement.ProductCurvatureMixedScalar.three_factor_charge_nonnegative

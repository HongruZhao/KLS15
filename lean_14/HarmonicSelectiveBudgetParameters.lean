import SelectiveBudgetTriangleYoung

/-! The optimal elementary parameters for the exact size-two budget
cancellation.  These are scalar identities and legal parameter ranges. -/
noncomputable section
namespace KLS.DeterministicBridgeNext
set_option maxHeartbeats 1500000

def harmonicBudgetDenom (b z : ℝ) : ℝ := 1+(1-2/(b*(b+1)))*z
def harmonicBudgetTheta (b z : ℝ) : ℝ := z/harmonicBudgetDenom b z
def harmonicBudgetEta (b z : ℝ) : ℝ := 1/harmonicBudgetDenom b z
def harmonicBudgetLambda (b z : ℝ) : ℝ := 2*z/(b*(b+1))

theorem harmonicBudgetDenom_ge_one {b z : ℝ} (hb : 2 ≤ b) (hz : 0 ≤ z) :
    1 ≤ harmonicBudgetDenom b z := by
  have hp : 0 < b*(b+1) := by positivity
  have hf : 2/(b*(b+1)) ≤ 1 := (div_le_iff₀ hp).2 (by nlinarith)
  unfold harmonicBudgetDenom
  nlinarith [mul_nonneg (sub_nonneg.mpr hf) hz]

theorem harmonicBudgetDenom_pos {b z : ℝ} (hb : 2 ≤ b) (hz : 0 ≤ z) :
    0 < harmonicBudgetDenom b z := lt_of_lt_of_le (by norm_num) (harmonicBudgetDenom_ge_one hb hz)

theorem harmonicBudgetLambda_lt_one {b z : ℝ} (hb : 2 ≤ b) (hcap : 2*z < b*(b+1)) :
    harmonicBudgetLambda b z < 1 := by
  have hp : 0 < b*(b+1) := by positivity
  exact (div_lt_one hp).2 hcap

theorem harmonicBudgetTheta_nonneg {b z : ℝ} (hb : 2 ≤ b) (hz : 0 ≤ z) :
    0 ≤ harmonicBudgetTheta b z := div_nonneg hz (harmonicBudgetDenom_pos hb hz).le

theorem harmonicBudgetTheta_lt_one {b z : ℝ} (hb : 2 ≤ b) (hz : 0 ≤ z)
    (hcap : 2*z < b*(b+1)) : harmonicBudgetTheta b z < 1 := by
  have hD := harmonicBudgetDenom_pos hb hz
  have hl := harmonicBudgetLambda_lt_one hb hcap
  have he : harmonicBudgetDenom b z-z = 1-harmonicBudgetLambda b z := by
    unfold harmonicBudgetDenom harmonicBudgetLambda
    ring
  unfold harmonicBudgetTheta
  apply (div_lt_one hD).2
  linarith

theorem harmonicBudgetEta_pos {b z : ℝ} (hb : 2 ≤ b) (hz : 0 ≤ z) :
    0 < harmonicBudgetEta b z := one_div_pos.mpr (harmonicBudgetDenom_pos hb hz)

theorem harmonicBudget_first_cost {b z : ℝ} (hb : 2 ≤ b) (hz : 0 ≤ z)
    (hcap : 2*z < b*(b+1)) :
    (1-harmonicBudgetTheta b z)^2/(1-harmonicBudgetLambda b z) +
      harmonicBudgetTheta b z*harmonicBudgetEta b z = 1/harmonicBudgetDenom b z := by
  have hD := harmonicBudgetDenom_pos hb hz
  have hl := harmonicBudgetLambda_lt_one hb hcap
  have hp : 0 < b*(b+1) := by positivity
  unfold harmonicBudgetTheta harmonicBudgetEta
  have he : harmonicBudgetDenom b z-z = 1-harmonicBudgetLambda b z := by
    unfold harmonicBudgetDenom harmonicBudgetLambda
    ring
  have he' : 1-harmonicBudgetTheta b z =
      (1-harmonicBudgetLambda b z)/harmonicBudgetDenom b z := by
    unfold harmonicBudgetTheta
    rw [←he]
    field_simp
  unfold harmonicBudgetTheta at he'
  rw [he']
  field_simp [ne_of_gt hD,ne_of_gt (sub_pos.mpr hl)]
  nlinarith [he]

theorem harmonicBudget_charge_identity {b z K s : ℝ} (hb : 2 ≤ b) (hz : 0 ≤ z)
    (hK : 0 < K) (hs : 0 < s) :
    harmonicBudgetLambda b z*b^2/(4*K*s) =
      harmonicBudgetTheta b z*b/(2*K*(b+1)*(harmonicBudgetEta b z*s)) := by
  have hD := harmonicBudgetDenom_pos hb hz
  have hb0 : b ≠ 0 := by linarith
  have hb1 : b+1 ≠ 0 := by linarith
  unfold harmonicBudgetLambda harmonicBudgetTheta harmonicBudgetEta
  field_simp [hb0,hb1,ne_of_gt hD,ne_of_gt hK,ne_of_gt hs]
  ring

theorem harmonicBudget_theta_div_eta {b z : ℝ} (hb : 2 ≤ b) (hz : 0 ≤ z) :
    harmonicBudgetTheta b z/harmonicBudgetEta b z = z := by
  have hD := harmonicBudgetDenom_pos hb hz
  unfold harmonicBudgetTheta harmonicBudgetEta
  field_simp

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.harmonicBudget_first_cost
#print axioms KLS.DeterministicBridgeNext.harmonicBudget_charge_identity

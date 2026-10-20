import SelectedRowsTriangleYoung

/-! Exact harmonic allocation for an arbitrary selected insertion row.
The ratio r is the coefficient of its canonical square divided by the
matching retained budget coefficient. No estimate of r is assumed here. -/
noncomputable section
namespace KLS.DeterministicBridgeNext
set_option maxHeartbeats 1500000

def selectedHarmonicDenom (r z : ℝ) : ℝ := 1+(1-r)*z
def selectedHarmonicTheta (r z : ℝ) : ℝ := z/selectedHarmonicDenom r z
def selectedHarmonicEta (r z : ℝ) : ℝ := 1/selectedHarmonicDenom r z
def selectedHarmonicLambda (r z : ℝ) : ℝ := r*z

theorem selectedHarmonicDenom_ge_one {r z : ℝ} (hr : r ≤ 1) (hz : 0 ≤ z) :
    1 ≤ selectedHarmonicDenom r z := by
  unfold selectedHarmonicDenom
  nlinarith [mul_nonneg (sub_nonneg.mpr hr) hz]

theorem selectedHarmonicDenom_pos {r z : ℝ} (hr : r ≤ 1) (hz : 0 ≤ z) :
    0 < selectedHarmonicDenom r z :=
  lt_of_lt_of_le (by norm_num) (selectedHarmonicDenom_ge_one hr hz)

theorem selectedHarmonicTheta_nonneg {r z : ℝ} (hr : r ≤ 1) (hz : 0 ≤ z) :
    0 ≤ selectedHarmonicTheta r z :=
  div_nonneg hz (selectedHarmonicDenom_pos hr hz).le

theorem selectedHarmonicTheta_lt_one {r z : ℝ} (hr : r ≤ 1) (hz : 0 ≤ z)
    (hcap : r*z < 1) : selectedHarmonicTheta r z < 1 := by
  unfold selectedHarmonicTheta
  apply (div_lt_one (selectedHarmonicDenom_pos hr hz)).mpr
  unfold selectedHarmonicDenom
  linarith

theorem selectedHarmonicEta_pos {r z : ℝ} (hr : r ≤ 1) (hz : 0 ≤ z) :
    0 < selectedHarmonicEta r z :=
  one_div_pos.mpr (selectedHarmonicDenom_pos hr hz)

theorem selectedHarmonic_first_cost {r z : ℝ} (hr : r ≤ 1) (hz : 0 ≤ z)
    (hcap : r*z < 1) :
    (1-selectedHarmonicTheta r z)^2/(1-selectedHarmonicLambda r z) +
      selectedHarmonicTheta r z*selectedHarmonicEta r z =
        1/selectedHarmonicDenom r z := by
  have hD := selectedHarmonicDenom_pos hr hz
  have hcap' : 0 < 1-r*z := sub_pos.mpr hcap
  unfold selectedHarmonicTheta selectedHarmonicEta selectedHarmonicLambda
  have he : selectedHarmonicDenom r z-z=1-r*z := by
    unfold selectedHarmonicDenom
    ring
  have he' : 1-z/selectedHarmonicDenom r z=(1-r*z)/selectedHarmonicDenom r z := by
    rw [←he]
    field_simp
  rw [he']
  field_simp [hD.ne',hcap'.ne']
  nlinarith [he]

theorem selectedHarmonic_theta_div_eta {r z : ℝ} (hr : r ≤ 1) (hz : 0 ≤ z) :
    selectedHarmonicTheta r z/selectedHarmonicEta r z=z := by
  have hD := selectedHarmonicDenom_pos hr hz
  unfold selectedHarmonicTheta selectedHarmonicEta
  field_simp

theorem selectedHarmonic_charge_identity {r z A s : ℝ}
    (hr : r ≤ 1) (hz : 0 ≤ z) (hs : 0 < s) :
    selectedHarmonicLambda r z*A/s =
      selectedHarmonicTheta r z*(r*A)/(selectedHarmonicEta r z*s) := by
  have hD := selectedHarmonicDenom_pos hr hz
  unfold selectedHarmonicTheta selectedHarmonicEta selectedHarmonicLambda
  field_simp [hD.ne',hs.ne']

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.selectedHarmonic_first_cost
#print axioms KLS.DeterministicBridgeNext.selectedHarmonic_charge_identity

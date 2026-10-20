import HarmonicSelectiveBudgetParameters
import TripleCreationBudgetAlgebra

/-! Exact harmonic scalar parameters for independently selected canonical
size-two and size-three squares. No probabilistic or spectral premise is
introduced here. The size-three ratio includes its factorial normalization. -/
noncomputable section
namespace KLS.DeterministicBridgeNext
set_option maxHeartbeats 1500000

abbrev harmonicRatioDenom := selectedHarmonicDenom
abbrev harmonicRatioTheta := selectedHarmonicTheta
abbrev harmonicRatioEta := selectedHarmonicEta
abbrev harmonicRatioLambda := selectedHarmonicLambda

theorem harmonicRatioDenom_ge_one {r z : ℝ} (hr : r ≤ 1) (hz : 0 ≤ z) :
    1 ≤ harmonicRatioDenom r z := selectedHarmonicDenom_ge_one hr hz

theorem harmonicRatioDenom_pos {r z : ℝ} (hr : r ≤ 1) (hz : 0 ≤ z) :
    0 < harmonicRatioDenom r z := selectedHarmonicDenom_pos hr hz

theorem harmonicRatioTheta_nonneg {r z : ℝ} (hr : r ≤ 1) (hz : 0 ≤ z) :
    0 ≤ harmonicRatioTheta r z := selectedHarmonicTheta_nonneg hr hz

theorem harmonicRatioTheta_lt_one {r z : ℝ} (hr : r ≤ 1) (hz : 0 ≤ z)
    (hcap : r*z < 1) : harmonicRatioTheta r z < 1 := selectedHarmonicTheta_lt_one hr hz hcap

theorem harmonicRatioEta_pos {r z : ℝ} (hr : r ≤ 1) (hz : 0 ≤ z) :
    0 < harmonicRatioEta r z := selectedHarmonicEta_pos hr hz

theorem harmonicRatio_theta_div_eta {r z : ℝ} (hr : r ≤ 1) (hz : 0 ≤ z) :
    harmonicRatioTheta r z/harmonicRatioEta r z = z := selectedHarmonic_theta_div_eta hr hz

theorem harmonicRatio_first_cost {r z : ℝ} (hr : r ≤ 1) (hz : 0 ≤ z)
    (hcap : r*z < 1) :
    (1-harmonicRatioTheta r z)^2/(1-harmonicRatioLambda r z)+
      harmonicRatioTheta r z*harmonicRatioEta r z = 1/harmonicRatioDenom r z :=
  selectedHarmonic_first_cost hr hz hcap

abbrev tripleHarmonicRatio := KLSBelow25.TripleCreation.chargeRatio
abbrev tripleCreationQCoefficient (b : ℝ) : ℝ := KLSBelow25.TripleCreation.affineQ (b+2)

theorem tripleHarmonicRatio_nonneg {b : ℝ} (hb : 2 ≤ b) :
    0 ≤ tripleHarmonicRatio b := by
  exact KLSBelow25.TripleCreation.chargeRatio_nonneg b hb

theorem tripleHarmonicRatio_le_one {b : ℝ} (hb : 2 ≤ b) :
    tripleHarmonicRatio b ≤ 1 := by
  have hp : 0 < b*(b+1)*(b+2) := by positivity
  have hf : b*(b+1)*(b+2)-6*(3*b-2) = (b-2)*(b-1)*(b+6) := by ring
  unfold tripleHarmonicRatio KLSBelow25.TripleCreation.chargeRatio
  apply (div_le_one hp).2
  nlinarith [mul_nonneg (mul_nonneg (by linarith : 0 ≤ b-2)
    (by linarith : 0 ≤ b-1)) (by linarith : 0 ≤ b+6)]

theorem tripleHarmonicRatio_lt_one {b : ℝ} (hb : 2 < b) :
    tripleHarmonicRatio b < 1 := KLSBelow25.TripleCreation.chargeRatio_lt_one b hb

theorem tripleHarmonicRatio_two : tripleHarmonicRatio 2 = 1 := by
  exact KLSBelow25.TripleCreation.chargeRatio_two

theorem tripleHarmonic_charge_coefficient {b K s : ℝ}
    (hb : 2 ≤ b) (hK : 0 < K) (hs : 0 < s) :
    tripleHarmonicRatio b*b^2/(36*K^2*s) =
      tripleCreationQCoefficient b/(K^2*(b+2)^2*(b+1)^2*s) := by
  have hb0 : b ≠ 0 := by linarith
  have hb1 : b+1 ≠ 0 := by linarith
  have hb2 : b+2 ≠ 0 := by linarith
  unfold tripleHarmonicRatio tripleCreationQCoefficient KLSBelow25.TripleCreation.chargeRatio
    KLSBelow25.TripleCreation.affineQ KLSBelow25.TripleCreation.chooseThree
  field_simp [hb0,hb1,hb2,ne_of_gt hK,ne_of_gt hs]
  ring

theorem tripleHarmonic_charge_identity {b z K s : ℝ}
    (hb : 2 ≤ b) (hz : 0 ≤ z) (hK : 0 < K) (hs : 0 < s) :
    harmonicRatioLambda (tripleHarmonicRatio b) z*b^2/(36*K^2*s) =
      harmonicRatioTheta (tripleHarmonicRatio b) z*tripleCreationQCoefficient b/
        (K^2*(b+2)^2*(b+1)^2*(harmonicRatioEta (tripleHarmonicRatio b) z*s)) := by
  have hD := harmonicRatioDenom_pos (tripleHarmonicRatio_le_one hb) hz
  have hb0 : b ≠ 0 := by linarith
  have hb1 : b+1 ≠ 0 := by linarith
  have hb2 : b+2 ≠ 0 := by linarith
  calc
    _ = z*(tripleHarmonicRatio b*b^2/(36*K^2*s)) := by
      unfold harmonicRatioLambda selectedHarmonicLambda
      ring
    _ = z*(tripleCreationQCoefficient b/(K^2*(b+2)^2*(b+1)^2*s)) := by
      rw [tripleHarmonic_charge_coefficient hb hK hs]
    _ = _ := by
      unfold harmonicRatioTheta harmonicRatioEta selectedHarmonicTheta selectedHarmonicEta
      field_simp [hb0,hb1,hb2,ne_of_gt hK,ne_of_gt hs,ne_of_gt hD]

theorem tripleHarmonic_rest_identity {b z K s R : ℝ}
    (hb : 2 ≤ b) (hz : 0 ≤ z) (hK : 0 < K) (hs : 0 < s) :
    harmonicRatioTheta (tripleHarmonicRatio b) z*R/
        (K^2*(b+2)^2*(b+1)^2*(harmonicRatioEta (tripleHarmonicRatio b) z*s)) =
      z*R/(K^2*(b+2)^2*(b+1)^2*s) := by
  have hD := harmonicRatioDenom_pos (tripleHarmonicRatio_le_one hb) hz
  have hb1 : b+1 ≠ 0 := by linarith
  have hb2 : b+2 ≠ 0 := by linarith
  unfold harmonicRatioTheta harmonicRatioEta selectedHarmonicTheta selectedHarmonicEta
  field_simp [hb1,hb2,ne_of_gt hK,ne_of_gt hs,ne_of_gt hD]

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.harmonicRatio_first_cost
#print axioms KLS.DeterministicBridgeNext.tripleHarmonic_charge_identity
#print axioms KLS.DeterministicBridgeNext.tripleHarmonic_rest_identity

import QuinticSmoothInverse

/-! The actual finite-rank scalar inequality in Proposition 3.1 after the
coefficient ratios and convolution bounds are supplied. No law or analytic
Appell induction is postulated here. -/
noncomputable section
namespace Quintic24886

def qPhi (u : ℝ) : ℝ := -deriv phi u / phi u
def convolutionWeight (k : ℝ) : ℝ := k*(k-1)/2-1+delta*(k+1)

theorem qPhi_positive {u : ℝ} (hu : u ∈ Set.Icc 0 1) : 0 < qPhi u := by
  have hp : 0 < phi u := by linarith [(phi_branch_of_unit hu).1.1]
  exact div_pos (neg_pos.mpr (deriv_phi_negative hu)) hp

theorem finite_rank_criterion {k u dk dj : ℝ} (hk : 3 ≤ k)
    (hu : u ∈ Set.Icc 0 1)
    (hdk : dk ≤ r * convolutionWeight k)
    (hdj : dj ≤ r * convolutionWeight (k+1)) :
    qPhi u * (alpha*K*(k+1)^2*phi u -
      (A*k^2+(A-3)*k+2)*u - 2*dk*Real.sqrt u) >
      2*(k+1)^2-(k+1)+2 + 2*dj/Real.sqrt (phi u) := by
  have hp : 0 < phi u := by linarith [(phi_branch_of_unit hu).1.1]
  have hs : 0 < Real.sqrt (phi u) := Real.sqrt_pos.mpr hp
  have hq := qPhi_positive hu
  have hr : 0 < r := by norm_num [r]
  have hj : 0 < k+1 := by linarith
  let t : ℝ := 1/(k+1)
  have ht : 0 < t := by dsimp [t]; positivity
  have ht4 : t ≤ 1/4 := by
    dsimp [t]
    apply (div_le_div_iff₀ hj (by norm_num : (0 : ℝ) < 4)).mpr
    linarith
  let bc := 1+(A+3)*(qPhi u*u)+(1-2*delta)*(r/Real.sqrt (phi u))+
    (3-2*delta)*(r*qPhi u*Real.sqrt u)
  let dc := -5*(qPhi u*u)+(2-2*delta)*(r/Real.sqrt (phi u))-2
  have hc : 0 < t*bc+t^2*dc := by
    exact finite_degree_correction_positive
      (mul_nonneg hq.le hu.1) (div_nonneg hr.le hs.le)
      (mul_nonneg (mul_nonneg hr.le hq.le) (Real.sqrt_nonneg u)) ht ht4
  have hm : 0 < phiMargin u + t*bc+t^2*dc := by
    linarith [phiMargin_positive hu]
  have heq :
      qPhi u*(alpha*K*(k+1)^2*phi u-
        (A*k^2+(A-3)*k+2)*u-2*r*convolutionWeight k*Real.sqrt u) -
        (2*(k+1)^2-(k+1)+2+
          2*r*convolutionWeight (k+1)/Real.sqrt (phi u)) =
      (k+1)^2*(phiMargin u+t*bc+t^2*dc) := by
    dsimp [qPhi, phiMargin, convolutionWeight, bc, dc, t]
    field_simp
    ring
  have hmaj : 0 < qPhi u*(alpha*K*(k+1)^2*phi u-
        (A*k^2+(A-3)*k+2)*u-2*r*convolutionWeight k*Real.sqrt u) -
        (2*(k+1)^2-(k+1)+2+
          2*r*convolutionWeight (k+1)/Real.sqrt (phi u)) := by
    rw [heq]
    exact mul_pos (sq_pos_of_pos hj) hm
  have hdkloss : 0 ≤ 2*qPhi u*(r*convolutionWeight k-dk)*Real.sqrt u := by
    exact mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hdk))
      (Real.sqrt_nonneg u)
  have hdjloss : 0 ≤ 2*(r*convolutionWeight (k+1)-dj)/Real.sqrt (phi u) := by
    exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hdj)) hs.le
  have halgebra :
      qPhi u*(alpha*K*(k+1)^2*phi u-
        (A*k^2+(A-3)*k+2)*u-2*dk*Real.sqrt u) -
        (2*(k+1)^2-(k+1)+2+2*dj/Real.sqrt (phi u)) =
      (qPhi u*(alpha*K*(k+1)^2*phi u-
        (A*k^2+(A-3)*k+2)*u-2*r*convolutionWeight k*Real.sqrt u) -
        (2*(k+1)^2-(k+1)+2+
          2*r*convolutionWeight (k+1)/Real.sqrt (phi u))) +
      2*qPhi u*(r*convolutionWeight k-dk)*Real.sqrt u+
      2*(r*convolutionWeight (k+1)-dj)/Real.sqrt (phi u) := by ring
  have : 0 < qPhi u*(alpha*K*(k+1)^2*phi u-
        (A*k^2+(A-3)*k+2)*u-2*dk*Real.sqrt u) -
        (2*(k+1)^2-(k+1)+2+2*dj/Real.sqrt (phi u)) := by
    rw [halgebra]
    linarith
  linarith

#print axioms finite_rank_criterion
end Quintic24886

import GenericFactorialConvolution

/-! The finite-degree correction is uniform over the pointwise choice of alpha.
The scalar margin is the only barrier-specific input. -/
noncomputable section
namespace KLS.DeterministicBridgeNext
set_option maxHeartbeats 2000000

def genericConvolutionWeight (delta k : ℝ) : ℝ := k*(k-1)/2-1+delta*(k+1)

theorem generic_finite_degree_correction_positive {A delta v rho sigma t : ℝ}
    (hA : 0 < A) (hdelta : delta < 1/2)
    (hv : 0 ≤ v) (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma)
    (ht : 0 < t) (htop : t ≤ 1/4) :
    0 < t*(1+(A+3)*v+(1-2*delta)*rho+(3-2*delta)*sigma)+
      t^2*(-5*v+(2-2*delta)*rho-2) := by
  let bc := 1+(A+3)*v+(1-2*delta)*rho+(3-2*delta)*sigma
  let dc := -5*v+(2-2*delta)*rho-2
  have h1 : 0 < A+3 := by linarith
  have h2 : 0 < 1-2*delta := by linarith
  have h3 : 0 < 3-2*delta := by linarith
  have h4 : 0 < A+7/4 := by linarith
  have h5 : 0 < 3/2-5*delta/2 := by linarith
  have hb : 0 < bc := by dsimp [bc]; positivity
  have hend : 0 < bc+dc/4 := by
    have he : bc+dc/4=1/2+(A+7/4)*v+(3/2-5*delta/2)*rho+(3-2*delta)*sigma := by
      dsimp [bc,dc]; ring
    rw [he]
    positivity
  have hp := KLSBelow25.affine_positive_of_endpoint hb hend ht.le htop
  have hm := mul_pos ht hp
  dsimp [bc,dc] at hm
  nlinarith

theorem generic_finite_rank_criterion {k u dk dj z q alpha K A r delta : ℝ}
    (hk : 3 ≤ k) (hu : u ∈ Set.Icc 0 1)
    (hp : 0 < z) (hq : 0 < q) (hr : 0 < r)
    (hA : 0 < A) (hdelta : delta < 1/2)
    (hmargin : 0 < q*(alpha*K*z-A*u-r*Real.sqrt u)-2-r/Real.sqrt z)
    (hdk : dk ≤ r*genericConvolutionWeight delta k)
    (hdj : dj ≤ r*genericConvolutionWeight delta (k+1)) :
    q*(alpha*K*(k+1)^2*z-(A*k^2+(A-3)*k+2)*u-2*dk*Real.sqrt u) >
      2*(k+1)^2-(k+1)+2+2*dj/Real.sqrt z := by
  have hs : 0 < Real.sqrt (z) := Real.sqrt_pos.mpr hp
  have hj : 0 < k+1 := by linarith
  let t : ℝ := 1/(k+1)
  have ht : 0 < t := by dsimp [t]; positivity
  have ht4 : t ≤ 1/4 := by
    dsimp [t]
    apply (div_le_div_iff₀ hj (by norm_num : (0 : ℝ) < 4)).mpr
    linarith
  let bc := 1+(A+3)*(q*u)+(1-2*delta)*(r/Real.sqrt (z))+
    (3-2*delta)*(r*q*Real.sqrt u)
  let dc := -5*(q*u)+(2-2*delta)*(r/Real.sqrt (z))-2
  have hc : 0 < t*bc+t^2*dc := by
    exact generic_finite_degree_correction_positive hA hdelta
      (mul_nonneg hq.le hu.1) (div_nonneg hr.le hs.le)
      (mul_nonneg (mul_nonneg hr.le hq.le) (Real.sqrt_nonneg u)) ht ht4
  have hm : 0 < q*(alpha*K*z-A*u-r*Real.sqrt u)-2-r/Real.sqrt z + t*bc+t^2*dc := by
    linarith [hmargin]
  have heq :
      q*(alpha*K*(k+1)^2*z-
        (A*k^2+(A-3)*k+2)*u-2*r*genericConvolutionWeight delta k*Real.sqrt u) -
        (2*(k+1)^2-(k+1)+2+
          2*r*genericConvolutionWeight delta (k+1)/Real.sqrt (z)) =
      (k+1)^2*(q*(alpha*K*z-A*u-r*Real.sqrt u)-2-r/Real.sqrt z+t*bc+t^2*dc) := by
    dsimp [genericConvolutionWeight, bc, dc, t]
    field_simp
    ring
  have hmaj : 0 < q*(alpha*K*(k+1)^2*z-
        (A*k^2+(A-3)*k+2)*u-2*r*genericConvolutionWeight delta k*Real.sqrt u) -
        (2*(k+1)^2-(k+1)+2+
          2*r*genericConvolutionWeight delta (k+1)/Real.sqrt (z)) := by
    rw [heq]
    exact mul_pos (sq_pos_of_pos hj) hm
  have hdkloss : 0 ≤ 2*q*(r*genericConvolutionWeight delta k-dk)*Real.sqrt u := by
    exact mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hdk))
      (Real.sqrt_nonneg u)
  have hdjloss : 0 ≤ 2*(r*genericConvolutionWeight delta (k+1)-dj)/Real.sqrt (z) := by
    exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hdj)) hs.le
  have halgebra :
      q*(alpha*K*(k+1)^2*z-
        (A*k^2+(A-3)*k+2)*u-2*dk*Real.sqrt u) -
        (2*(k+1)^2-(k+1)+2+2*dj/Real.sqrt (z)) =
      (q*(alpha*K*(k+1)^2*z-
        (A*k^2+(A-3)*k+2)*u-2*r*genericConvolutionWeight delta k*Real.sqrt u) -
        (2*(k+1)^2-(k+1)+2+
          2*r*genericConvolutionWeight delta (k+1)/Real.sqrt (z))) +
      2*q*(r*genericConvolutionWeight delta k-dk)*Real.sqrt u+
      2*(r*genericConvolutionWeight delta (k+1)-dj)/Real.sqrt (z) := by ring
  have : 0 < q*(alpha*K*(k+1)^2*z-
        (A*k^2+(A-3)*k+2)*u-2*dk*Real.sqrt u) -
        (2*(k+1)^2-(k+1)+2+2*dj/Real.sqrt (z)) := by
    rw [halgebra]
    linarith
  linarith

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.generic_finite_rank_criterion

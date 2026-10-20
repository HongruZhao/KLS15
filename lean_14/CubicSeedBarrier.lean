import QuinticConvolution

/-! An actual smooth inverse for the paper's degree-three quadratic barrier.
This proves the scalar criterion, not the analytic Appell induction theorem. -/
noncomputable section
namespace CubicSeedBarrier

def B : ℝ := 121/4
def alpha : ℝ := 7/13
def A : ℝ := 20/3
def U (z : ℝ) : ℝ := 7/117*(1-z)*(65*z+1)
def Up (z : ℝ) : ℝ := (448-910*z)/117
def disc (u : ℝ) : ℝ := 4356-(30420/7)*u
def phi (u : ℝ) : ℝ := (64+Real.sqrt (disc u))/130
def phiD (u : ℝ) : ℝ := -(30420/7)/(260*Real.sqrt (disc u))
def phiDD (u : ℝ) : ℝ := -(30420/7)^2/(520*(Real.sqrt (disc u))^3)
def q (u : ℝ) : ℝ := -deriv phi u/phi u
def domain : Set ℝ := Set.Iio (1001/1000)

theorem disc_positive {u : ℝ} (hu : u ∈ domain) : 0 < disc u := by
  change u < (1001/1000 : ℝ) at hu
  dsimp [disc]
  linarith

theorem unit_in_domain {u : ℝ} (hu : u ∈ Set.Icc 0 1) : u ∈ domain := by
  change u < (1001/1000 : ℝ)
  linarith [hu.2]

theorem contDiffAt_phi {u : ℝ} (hu : u ∈ domain) :
    ContDiffAt ℝ (⊤ : ℕ∞) phi u := by
  have hd : ContDiffAt ℝ (⊤ : ℕ∞) disc u := by unfold disc; fun_prop
  have hs : ContDiffAt ℝ (⊤ : ℕ∞) (fun v => Real.sqrt (disc v)) u :=
    hd.sqrt (ne_of_gt (disc_positive hu))
  have hc : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : ℝ => (64 : ℝ)) u := contDiffAt_const
  exact (hc.add hs).div_const 130

theorem hasDerivAt_disc (u : ℝ) : HasDerivAt disc (-(30420/7)) u := by
  convert (hasDerivAt_const u (4356 : ℝ)).sub
    ((hasDerivAt_id' u).const_mul (30420/7)) using 1 <;>
    first | rfl | (simp [disc] <;> ring)

theorem hasDerivAt_phi {u : ℝ} (hu : u ∈ domain) : HasDerivAt phi (phiD u) u := by
  have hs := (hasDerivAt_disc u).sqrt (ne_of_gt (disc_positive hu))
  convert (hs.const_add 64).div_const 130 using 1 <;>
    first | rfl | (simp [phi,phiD] <;> ring)

theorem hasDerivAt_phiD {u : ℝ} (hu : u ∈ domain) :
    HasDerivAt phiD (phiDD u) u := by
  have hs := (hasDerivAt_disc u).sqrt (ne_of_gt (disc_positive hu))
  have hne : Real.sqrt (disc u) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (disc_positive hu))
  have hi := hs.inv hne
  convert hi.const_mul (-(30420/7)/260) using 1
  · ext v; dsimp [phiD]; ring
  · dsimp [phiDD]
    field_simp
    ring

theorem hasDerivAt_deriv_phi {u : ℝ} (hu : u ∈ domain) :
    HasDerivAt (deriv phi) (phiDD u) u := by
  have hevent : deriv phi =ᶠ[nhds u] phiD := by
    filter_upwards [isOpen_Iio.mem_nhds hu] with v hv
    exact (hasDerivAt_phi hv).deriv
  exact (hasDerivAt_phiD hu).congr_of_eventuallyEq hevent

theorem phi_range {u : ℝ} (hu : u ∈ Set.Icc 0 1) :
    1/2 < phi u ∧ phi u ≤ 1 := by
  have hd := disc_positive (unit_in_domain hu)
  have hs : (Real.sqrt (disc u))^2 = 4356-(30420/7)*u := Real.sq_sqrt hd.le
  have hs0 := Real.sqrt_nonneg (disc u)
  have hl : 1 < Real.sqrt (disc u) := by
    nlinarith [hu.2]
  have hh : Real.sqrt (disc u) ≤ 66 := by
    nlinarith [hu.1]
  dsimp [phi]
  constructor <;> linarith

theorem phi_zero : phi 0 = 1 := by norm_num [phi,disc]

theorem inverse_identity {u : ℝ} (hu : u ∈ domain) : U (phi u) = u := by
  have hs : (Real.sqrt (disc u))^2 = 4356-(30420/7)*u :=
    Real.sq_sqrt (disc_positive hu).le
  dsimp [U,phi]
  nlinarith

theorem inverse_derivative_identity {u : ℝ} (hu : u ∈ domain) :
    phiD u*Up (phi u) = 1 := by
  have hne := ne_of_gt (Real.sqrt_pos.mpr (disc_positive hu))
  dsimp [phiD,Up,phi]
  field_simp
  ring

theorem polynomial_barrier_identity (z : ℝ) :
    (18*z+9/16)*Up z = 36*U z-(9/2)*alpha*B*z := by
  norm_num [Up,U,alpha,B]
  ring

theorem derivative_negative {u : ℝ} (hu : u ∈ domain) : deriv phi u < 0 := by
  rw [(hasDerivAt_phi hu).deriv]
  dsimp [phiD]
  have hs := Real.sqrt_pos.mpr (disc_positive hu)
  exact div_neg_of_neg_of_pos (by norm_num) (by positivity)

theorem derivative2_negative {u : ℝ} (hu : u ∈ domain) : deriv (deriv phi) u < 0 := by
  rw [(hasDerivAt_deriv_phi hu).deriv]
  dsimp [phiDD]
  have hs := Real.sqrt_pos.mpr (disc_positive hu)
  exact div_neg_of_neg_of_pos (by norm_num) (by positivity)

theorem strictAntiOn_phi : StrictAntiOn phi (Set.Icc 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · intro u hu
    exact (contDiffAt_phi (unit_in_domain hu)).continuousAt.continuousWithinAt
  · intro u hu
    exact derivative_negative (unit_in_domain (interior_subset hu))

theorem strictConcaveOn_phi : StrictConcaveOn ℝ (Set.Icc 0 1) phi := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _)
  · intro u hu
    exact (contDiffAt_phi (unit_in_domain hu)).continuousAt.continuousWithinAt
  · intro u hu
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using
      derivative2_negative (unit_in_domain (interior_subset hu))

theorem cubic_margin_positive {u : ℝ} (hu : u ∈ Set.Icc 0 1) :
    0 < (-deriv phi u)*((9/2)*alpha*B*phi u-36*u)-
      17*phi u-(16/11)*Real.sqrt (phi u) := by
  have hdom := unit_in_domain hu
  have hi := inverse_identity hdom
  have hd := inverse_derivative_identity hdom
  have hb := polynomial_barrier_identity (phi u)
  have heq : (-deriv phi u)*((9/2)*alpha*B*phi u-36*u) =
      18*phi u+9/16 := by
    rw [(hasDerivAt_phi hdom).deriv]
    rw [hi] at hb
    calc
      (-phiD u)*((9/2)*alpha*B*phi u-36*u) =
          phiD u*((18*phi u+9/16)*Up (phi u)) := by rw [hb]; ring
      _ = (18*phi u+9/16)*(phiD u*Up (phi u)) := by ring
      _ = 18*phi u+9/16 := by rw [hd]; ring
  rw [heq]
  have hp : 0 ≤ phi u := le_of_lt (lt_trans (by norm_num) (phi_range hu).1)
  have hs := Real.sq_sqrt hp
  nlinarith [sq_nonneg (Real.sqrt (phi u)-8/11)]

theorem cubic_scalar_criterion {u : ℝ} (hu : u ∈ Set.Icc 0 1) :
    q u*((9/2)*alpha*B*phi u-(6*A-4)*u) >
      17+8/Real.sqrt (B*phi u) := by
  have hm := cubic_margin_positive hu
  have hp : 0 < phi u := lt_trans (by norm_num) (phi_range hu).1
  have hs := Real.sqrt_pos.mpr hp
  have he : (Real.sqrt (phi u))^2 = phi u := Real.sq_sqrt hp.le
  have hB : Real.sqrt B = 11/2 := by norm_num [B]
  have hne := ne_of_gt hp
  have hsne := ne_of_gt hs
  have hmul :
      (q u*((9/2)*alpha*B*phi u-(6*A-4)*u)-
        (17+8/Real.sqrt (B*phi u)))*phi u =
      (-deriv phi u)*((9/2)*alpha*B*phi u-36*u)-
        17*phi u-(16/11)*Real.sqrt (phi u) := by
    rw [Real.sqrt_mul (by norm_num [B] : (0 : ℝ) ≤ B), hB]
    dsimp [q,A]
    field_simp
    nlinarith
  nlinarith

theorem alpha_mem_unit : alpha ∈ Set.Ioo (0 : ℝ) 1 := by norm_num [alpha]
theorem A_formula : A = 4/(1-alpha)-2 := by norm_num [A,alpha]

theorem coefficientH_three : Quintic24886.coefficientH 3 = 1089 := by
  rw [Quintic24886.coefficientH_ge_three (by omega)]
  norm_num [Quintic24886.B, Nat.factorial]

theorem coefficientD_two : Quintic24886.coefficientD 2 = 0 := by
  norm_num [Quintic24886.coefficientD]

theorem coefficientD_three : Quintic24886.coefficientD 3 = 24 := by
  norm_num [Quintic24886.coefficientD, Quintic24886.coefficientH_two]

theorem original_degree_three_criterion {u : ℝ} (hu : u ∈ Set.Icc 0 1) :
    q u * (alpha * (Quintic24886.coefficientH 3 / Quintic24886.coefficientH 2) * phi u -
      (A*2^2+(A-3)*2+2)*u -
      2*Quintic24886.coefficientD 2/Real.sqrt (Quintic24886.coefficientH 2)*Real.sqrt u) >
      2*3^2-3+2+2*Quintic24886.coefficientD 3/
        Real.sqrt (Quintic24886.coefficientH 3*phi u) := by
  have hp : 0 ≤ phi u := le_of_lt (lt_trans (by norm_num) (phi_range hu).1)
  rw [coefficientH_three, Quintic24886.coefficientH_two,
    coefficientD_two, coefficientD_three]
  have he : Real.sqrt ((1089 : ℝ)*phi u) = 6*Real.sqrt (B*phi u) := by
    have heq : (1089 : ℝ)*phi u = 36*(B*phi u) := by norm_num [B]; ring
    rw [heq, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 36)]
    norm_num
  rw [he]
  convert cubic_scalar_criterion hu using 1 <;> norm_num [B,A] <;> ring <;> simp_all

#print axioms contDiffAt_phi
#print axioms strictConcaveOn_phi
#print axioms original_degree_three_criterion
end CubicSeedBarrier

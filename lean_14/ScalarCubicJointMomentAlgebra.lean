import Mathlib

/-! Exact completion of the scalar sharp cubic and sixth-cumulant bounds.

The hypotheses are explicit moment comparisons. This module does not
prove those comparisons from log-concavity and is not an unconditional
log-concave theorem. The mathematical discharge is recorded separately in
research/cubic-cap-scalar-sharp-proof.md. -/
noncomputable section
open MeasureTheory
namespace KLSImprovement.ScalarJointMoments
set_option backward.isDefEq.respectTransparency false

def scalarCubicVariance (m3 m4 m6 : ℝ) : ℝ := m6-6*m4+9-m3^2
def scalarSixthCumulant (m3 m4 m6 : ℝ) : ℝ := m6-15*m4-10*m3^2+30

theorem cubic_variance_cumulant_decomposition (m3 m4 m6 : ℝ) :
    scalarCubicVariance m3 m4 m6 = scalarSixthCumulant m3 m4 m6+
      9*(m4-3)+9*m3^2+6 := by
  unfold scalarCubicVariance scalarSixthCumulant
  ring

theorem cubic_le_216_of_scalar_cumulant_bounds {m3 m4 m6 : ℝ}
    (h6 : scalarSixthCumulant m3 m4 m6 ≤ 120)
    (h4 : m4 ≤ 9) (h3 : m3^2 ≤ 4) :
    scalarCubicVariance m3 m4 m6 ≤ 216 := by
  rw [cubic_variance_cumulant_decomposition]
  linarith

theorem exponential_values_attain :
    scalarCubicVariance 2 9 265 = 216 ∧ scalarSixthCumulant 2 9 265 = 120 := by
  norm_num [scalarCubicVariance, scalarSixthCumulant]

theorem cubic_joint_moment_completion {m3 m4 m6 q : ℝ}
    (hlinear : 9*m6 ≤ 265*m4)
    (hskew : m3^2 = 4-12*q^2-8*q^3)
    (hsix : m6 ≤ 265-660*q^2-80*q^3) :
    scalarCubicVariance m3 m4 m6 ≤
      216-(27216/53 : ℝ)*q^2-(2952/53 : ℝ)*q^3 := by
  have hfirst : scalarCubicVariance m3 m4 m6 ≤
      (211/265 : ℝ)*m6+9-m3^2 := by
    unfold scalarCubicVariance
    linarith
  calc
    _ ≤ (211/265 : ℝ)*m6+9-m3^2 := hfirst
    _ ≤ (211/265 : ℝ)*(265-660*q^2-80*q^3)+9-m3^2 := by linarith
    _ = _ := by rw [hskew]; ring

theorem sixth_cumulant_joint_moment_completion {m3 m4 m6 q : ℝ}
    (hlinear : 9*m6 ≤ 265*m4)
    (hskew : m3^2 = 4-12*q^2-8*q^3)
    (hsix : m6 ≤ 265-660*q^2-80*q^3) :
    scalarSixthCumulant m3 m4 m6 ≤
      120-(2160/53 : ℝ)*q^2*(5-q) := by
  have hfirst : scalarSixthCumulant m3 m4 m6 ≤
      (26/53 : ℝ)*m6-10*m3^2+30 := by
    unfold scalarSixthCumulant
    linarith
  calc
    _ ≤ (26/53 : ℝ)*m6-10*m3^2+30 := hfirst
    _ ≤ (26/53 : ℝ)*(265-660*q^2-80*q^3)-10*m3^2+30 := by linarith
    _ = _ := by rw [hskew]; ring

theorem cubic_le_216_of_joint_moment_bounds {m3 m4 m6 q : ℝ}
    (hq : 0 ≤ q) (hlinear : 9*m6 ≤ 265*m4)
    (hskew : m3^2 = 4-12*q^2-8*q^3)
    (hsix : m6 ≤ 265-660*q^2-80*q^3) :
    scalarCubicVariance m3 m4 m6 ≤ 216 := by
  have h := cubic_joint_moment_completion hlinear hskew hsix
  have h2 := sq_nonneg q
  have h3 := pow_nonneg hq 3
  linarith

theorem sixth_cumulant_le_120_of_joint_moment_bounds {m3 m4 m6 q : ℝ}
    (hq : q ≤ 1/2) (hlinear : 9*m6 ≤ 265*m4)
    (hskew : m3^2 = 4-12*q^2-8*q^3)
    (hsix : m6 ≤ 265-660*q^2-80*q^3) :
    scalarSixthCumulant m3 m4 m6 ≤ 120 := by
  have h := sixth_cumulant_joint_moment_completion hlinear hskew hsix
  have hn : 0 ≤ (2160/53 : ℝ)*q^2*(5-q) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg q)) (by linarith)
  linarith

theorem cubic_lt_216_of_nonzero_skew_parameter {m3 m4 m6 q : ℝ}
    (hq : 0 < q) (hlinear : 9*m6 ≤ 265*m4)
    (hskew : m3^2 = 4-12*q^2-8*q^3)
    (hsix : m6 ≤ 265-660*q^2-80*q^3) :
    scalarCubicVariance m3 m4 m6 < 216 := by
  have h := cubic_joint_moment_completion hlinear hskew hsix
  have h2 : 0 < q^2 := pow_pos hq 2
  have h3 : 0 ≤ q^3 := pow_nonneg hq.le 3
  linarith

def moment (μ : Measure ℝ) (k : ℕ) : ℝ := ∫ x, x^k ∂μ

theorem centered_cubic_square_integral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : ∀ k ≤ 6, Integrable (fun x : ℝ => x^k) μ)
    (hmean : moment μ 1 = 0) (hvariance : moment μ 2 = 1) :
    (∫ x, (x^3-3*x-moment μ 3)^2 ∂μ) =
      scalarCubicVariance (moment μ 3) (moment μ 4) (moment μ 6) := by
  let c := moment μ 3
  have h6 := hm 6 le_rfl
  have h4 := hm 4 (by norm_num)
  have h3 := hm 3 (by norm_num)
  have h2 := hm 2 (by norm_num)
  have h1 : Integrable (fun x : ℝ => x) μ := by simpa using hm 1 (by norm_num)
  have he : (fun x : ℝ => (x^3-3*x-c)^2) =
      (fun x => x^6-6*x^4-2*c*x^3+9*x^2+6*c*x+c^2) := by
    funext x
    ring
  have hi64 : Integrable (fun x : ℝ => x^6-6*x^4) μ :=
    h6.sub (h4.const_mul 6)
  have hi643 : Integrable (fun x : ℝ => x^6-6*x^4-2*c*x^3) μ :=
    hi64.sub (h3.const_mul (2*c))
  have hi6432 : Integrable (fun x : ℝ => x^6-6*x^4-2*c*x^3+9*x^2) μ :=
    hi643.add (h2.const_mul 9)
  have hi64321 : Integrable (fun x : ℝ => x^6-6*x^4-2*c*x^3+9*x^2+6*c*x) μ :=
    hi6432.add (h1.const_mul (6*c))
  have hic : Integrable (fun _ : ℝ => c^2) μ := integrable_const _
  have hm1 : (∫ x : ℝ, x ∂μ) = 0 := by simpa [moment] using hmean
  have hm2 : (∫ x : ℝ, x^2 ∂μ) = 1 := hvariance
  change (∫ x, (x^3-3*x-c)^2 ∂μ) = _
  rw [he, integral_add hi64321 hic,
    integral_add hi6432 (h1.const_mul (6*c)),
    integral_add hi643 (h2.const_mul 9),
    integral_sub hi64 (h3.const_mul (2*c)), integral_sub h6 (h4.const_mul 6)]
  rw [integral_const_mul (6*c) (fun x : ℝ => x)]
  simp only [integral_const_mul, integral_const, probReal_univ, smul_eq_mul,
    one_mul, hm1, hm2]
  unfold scalarCubicVariance moment
  dsimp [c, moment]
  ring

/-- A measure-level corollary whose literature comparison inputs are explicit.
It must not be cited as a completed formal proof from log-concavity alone. -/
theorem scalar_cubic_cap_six_of_joint_moment_comparisons
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hm : ∀ k ≤ 6, Integrable (fun x : ℝ => x^k) μ)
    (hmean : moment μ 1 = 0) (hvariance : moment μ 2 = 1)
    (hlinear : 9*moment μ 6 ≤ 265*moment μ 4)
    (hjoint : ∃ q : ℝ, 0 ≤ q ∧ q ≤ 1/2 ∧
      (moment μ 3)^2 = 4-12*q^2-8*q^3 ∧
      moment μ 6 ≤ 265-660*q^2-80*q^3) :
    (∫ x, (x^3-3*x-moment μ 3)^2 ∂μ)/36 ≤ 6 := by
  rcases hjoint with ⟨q, hq, _, hskew, hsix⟩
  rw [centered_cubic_square_integral μ hm hmean hvariance]
  have h := cubic_le_216_of_joint_moment_bounds hq hlinear hskew hsix
  linarith

end KLSImprovement.ScalarJointMoments
#print axioms KLSImprovement.ScalarJointMoments.cubic_joint_moment_completion
#print axioms KLSImprovement.ScalarJointMoments.sixth_cumulant_joint_moment_completion
#print axioms KLSImprovement.ScalarJointMoments.cubic_variance_cumulant_decomposition
#print axioms KLSImprovement.ScalarJointMoments.cubic_le_216_of_scalar_cumulant_bounds
#print axioms KLSImprovement.ScalarJointMoments.centered_cubic_square_integral
#print axioms KLSImprovement.ScalarJointMoments.scalar_cubic_cap_six_of_joint_moment_comparisons

import TwoConeActualCubicCap
import TwoConeLogConcave

/-! A proved family extension of the full cubic bound. Every probability,
log-concavity and moment premise is discharged for the actual two-cone
law. The bound is stated in its covariance tensor metric; it is not a
universal log-concave theorem. -/
noncomputable section
open MeasureTheory MvPolynomial
namespace KLSImprovement.TwoConeFamily
open KLS KLSImprovement.TwoConeMoments KLSImprovement.TwoConeActualCubic
open KLSImprovement.SingleSlotCounterexample (Poly polyEval)
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem actual_mean_zero {d:ℝ} (hd:0 < d) (g:ℝ):
    rawMoment d g (z0 d g)=0 ∧ rawMoment d g (z1 d g)=0 := by
  rw [rawMoment_eq_qMoment hd.le,rawMoment_eq_qMoment hd.le,mean_z0 hd.le,mean_z1 hd.le]
  exact ⟨rfl,rfl⟩

theorem actual_covariance {d:ℝ} (hd:0 < d) (g:ℝ):
    rawMoment d g (z0 d g*z0 d g)=cov00 d g ∧
    rawMoment d g (z0 d g*z1 d g)=cov01 d g ∧
    rawMoment d g (z1 d g*z1 d g)=cov11 d g := by
  rw [rawMoment_eq_qMoment hd.le,rawMoment_eq_qMoment hd.le,rawMoment_eq_qMoment hd.le,
    second_z0 hd.le,second_cross hd.le,second_z1 hd.le]
  exact ⟨rfl,rfl,rfl⟩

theorem covariance_det_positive {d:ℝ} (hd:0 < d) (g:ℝ):
    0 < cov00 d g*cov11 d g-cov01 d g^2 := by
  have he : cov00 d g*cov11 d g-cov01 d g^2=1+d^2+2*d*g^2 := by
    unfold cov00 cov01 cov11
    ring
  rw [he]
  positivity

theorem actual_appell30_formula {d:ℝ} (hd:0 < d) (g:ℝ):
    appell30 d g=z0 d g^3-
      C (3*rawMoment d g (z0 d g*z0 d g))*z0 d g-
      C (rawMoment d g (z0 d g^3)) := by
  rw [(actual_covariance hd g).1,rawMoment_eq_qMoment hd.le,third_moment_0 hd.le]
  rfl

theorem actual_appell21_formula {d:ℝ} (hd:0 < d) (g:ℝ):
    appell21 d g=z0 d g^2*z1 d g-
      C (rawMoment d g (z0 d g*z0 d g))*z1 d g-
      C (2*rawMoment d g (z0 d g*z1 d g))*z0 d g-
      C (rawMoment d g (z0 d g^2*z1 d g)) := by
  rw [(actual_covariance hd g).1,(actual_covariance hd g).2.1,
    rawMoment_eq_qMoment hd.le,third_moment_1 hd.le]
  rfl

theorem actual_appell12_formula {d:ℝ} (hd:0 < d) (g:ℝ):
    appell12 d g=z0 d g*z1 d g^2-
      C (rawMoment d g (z1 d g*z1 d g))*z0 d g-
      C (2*rawMoment d g (z0 d g*z1 d g))*z1 d g-
      C (rawMoment d g (z0 d g*z1 d g^2)) := by
  rw [(actual_covariance hd g).2.2,(actual_covariance hd g).2.1,
    rawMoment_eq_qMoment hd.le,third_moment_2 hd.le]
  rfl

theorem actual_appell03_formula {d:ℝ} (hd:0 < d) (g:ℝ):
    appell03 d g=z1 d g^3-
      C (3*rawMoment d g (z1 d g*z1 d g))*z1 d g-
      C (rawMoment d g (z1 d g^3)) := by
  rw [(actual_covariance hd g).2.2,rawMoment_eq_qMoment hd.le,third_moment_3 hd.le]
  rfl

/-- All law hypotheses and the full four-coefficient cubic bound together.
The quantifier is the explicit two-cone family, not all log-concave laws. -/
theorem actual_two_cone_full_cubic_cap {d g:ℝ} (hd:0 < d) (hg:0≤g) (hg1:g≤1):
    IsProbabilityMeasure (rawMeasure d g) ∧ measureLogConcave (rawMeasure d g) ∧
      ∀x y z w:ℝ,
        (∫u,polyEval (cubicPolynomial d g x y z w) u^2 ∂rawMeasure d g)≤
          216*covarianceTensorQuadratic d g x y z w := by
  exact ⟨raw_isProbability hd.le g,TwoConeLogConcave.raw_logConcave hd hg hg1,
    actual_cubic_covariance_cap hd hg hg1⟩

theorem product_boundary_coordinate_equality {d:ℝ} (hd:0 < d):
    (∫u,polyEval (cubicPolynomial d 1 1 0 0 0) u^2 ∂rawMeasure d 1)=
      216*covarianceTensorQuadratic d 1 1 0 0 0 := by
  have he : (fun u:Space 2=>polyEval (cubicPolynomial d 1 1 0 0 0) u^2)=
      (fun u=>polyEval (cubicPolynomial d 1 1 0 0 0^2) u) := by
    funext u
    simp only [polyEval,MvPolynomial.eval_pow]
  rw [he]
  change rawMoment d 1 (cubicPolynomial d 1 1 0 0 0^2)=_
  rw [rawMoment_eq_qMoment hd.le,qMoment_cubicPolynomial_sq hd.le]
  unfold gramQuadratic covarianceTensorQuadratic CubicFourByFour.quadratic
    cov00 cov01 cov11 k00 k11 k22 k33 k01 k02 k03 k12 k13 k23
  ring

/-- Raw 216, equivalently normalized six, cannot be lowered uniformly
over this family. The coordinate test is an actual integrable polynomial. -/
theorem covariance_cap_is_sharp {C:ℝ}
    (hC : ∀ d g : ℝ, 0 < d → 0 ≤ g → g ≤ 1 → ∀ x y z w : ℝ,
      (∫u,polyEval (cubicPolynomial d g x y z w) u^2 ∂rawMeasure d g) ≤
        C*covarianceTensorQuadratic d g x y z w) : 216 ≤ C := by
  have h:=hC 1 1 (by norm_num) (by norm_num) (by norm_num) 1 0 0 0
  rw [product_boundary_coordinate_equality (by norm_num : (0:ℝ)<1)] at h
  norm_num [covarianceTensorQuadratic,CubicFourByFour.quadratic,cov00,cov01,cov11] at h ⊢
  linarith

end KLSImprovement.TwoConeFamily
#print axioms KLSImprovement.TwoConeFamily.actual_covariance
#print axioms KLSImprovement.TwoConeFamily.actual_appell21_formula
#print axioms KLSImprovement.TwoConeFamily.actual_two_cone_full_cubic_cap
#print axioms KLSImprovement.TwoConeFamily.product_boundary_coordinate_equality
#print axioms KLSImprovement.TwoConeFamily.covariance_cap_is_sharp

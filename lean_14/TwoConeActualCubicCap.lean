import TwoConePolynomialMoments
import TwoConeCubicMatrix

/-! Actual centered and cubic Appell moments for the two-cone family.
The matrix cap is connected to actual integrals, without moment inputs. -/
noncomputable section
open MeasureTheory MvPolynomial
open scoped BigOperators
namespace KLSImprovement.TwoConeActualCubic
open KLS KLSImprovement.CubicFourByFour KLSImprovement.TwoConeMoments
open KLSImprovement.TwoConeCubic
open KLSImprovement.SingleSlotCounterexample (Poly polyEval)
set_option maxHeartbeats 10000000
set_option maxRecDepth 5000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem qMoment_m00 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^0*X 1^0)=1 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

theorem qMoment_m01 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^0*X 1^1)=-d+1 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

theorem qMoment_m02 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^0*X 1^2)=2*d^2-2*d+2 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

theorem qMoment_m03 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^0*X 1^3)=-6*d^3+6*d^2-6*d+6 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

theorem qMoment_m04 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^0*X 1^4)=24*d^4-24*d^3+24*d^2-24*d+24 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

theorem qMoment_m05 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^0*X 1^5)=-120*d^5+120*d^4-120*d^3+120*d^2-120*d+120 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

theorem qMoment_m06 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^0*X 1^6)=720*d^6-720*d^5+720*d^4-720*d^3+720*d^2-720*d+720 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

theorem qMoment_m10 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^1*X 1^0)=d*g+1 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

theorem qMoment_m11 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^1*X 1^1)=-2*d^2*g-d+1 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

theorem qMoment_m12 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^1*X 1^2)=6*d^3*g+2*d^2-2*d+2 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

theorem qMoment_m13 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^1*X 1^3)=-24*d^4*g-6*d^3+6*d^2-6*d+6 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

theorem qMoment_m14 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^1*X 1^4)=120*d^5*g+24*d^4-24*d^3+24*d^2-24*d+24 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

theorem qMoment_m15 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^1*X 1^5)=-720*d^6*g-120*d^5+120*d^4-120*d^3+120*d^2-120*d+120 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

theorem qMoment_m20 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^2*X 1^0)=2*d^2*g^2+2*d*g^2+2*d*g+2 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

theorem qMoment_m21 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^2*X 1^1)=-6*d^3*g^2-6*d^2*g^2-4*d^2*g-2*d+2 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

theorem qMoment_m22 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^2*X 1^2)=24*d^4*g^2+24*d^3*g^2+12*d^3*g+4*d^2-4*d+4 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

theorem qMoment_m23 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^2*X 1^3)=-120*d^5*g^2-120*d^4*g^2-48*d^4*g-12*d^3+12*d^2-12*d+12 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

theorem qMoment_m24 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^2*X 1^4)=720*d^6*g^2+720*d^5*g^2+240*d^5*g+48*d^4-48*d^3+48*d^2-48*d+48 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

theorem qMoment_m30 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^3*X 1^0)=6*d^3*g^3+12*d^2*g^3+6*d^2*g^2+6*d*g^3+6*d*g^2+6*d*g+6 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

theorem qMoment_m31 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^3*X 1^1)=-24*d^4*g^3-48*d^3*g^3-18*d^3*g^2-24*d^2*g^3-18*d^2*g^2-12*d^2*g-6*d+6 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

theorem qMoment_m32 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^3*X 1^2)=120*d^5*g^3+240*d^4*g^3+72*d^4*g^2+120*d^3*g^3+72*d^3*g^2+36*d^3*g+12*d^2-12*d+12 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

theorem qMoment_m33 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^3*X 1^3)=-720*d^6*g^3-1440*d^5*g^3-360*d^5*g^2-720*d^4*g^3-360*d^4*g^2-144*d^4*g-36*d^3+36*d^2-36*d+36 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

theorem qMoment_m40 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^4*X 1^0)=24*d^4*g^4+72*d^3*g^4+24*d^3*g^3+72*d^2*g^4+48*d^2*g^3+24*d^2*g^2+24*d*g^4+24*d*g^3+24*d*g^2+24*d*g+24 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

theorem qMoment_m41 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^4*X 1^1)=-120*d^5*g^4-360*d^4*g^4-96*d^4*g^3-360*d^3*g^4-192*d^3*g^3-72*d^3*g^2-120*d^2*g^4-96*d^2*g^3-72*d^2*g^2-48*d^2*g-24*d+24 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

theorem qMoment_m42 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^4*X 1^2)=720*d^6*g^4+2160*d^5*g^4+480*d^5*g^3+2160*d^4*g^4+960*d^4*g^3+288*d^4*g^2+720*d^3*g^4+480*d^3*g^3+288*d^3*g^2+144*d^3*g+48*d^2-48*d+48 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

theorem qMoment_m50 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^5*X 1^0)=120*d^5*g^5+480*d^4*g^5+120*d^4*g^4+720*d^3*g^5+360*d^3*g^4+120*d^3*g^3+480*d^2*g^5+360*d^2*g^4+240*d^2*g^3+120*d^2*g^2+120*d*g^5+120*d*g^4+120*d*g^3+120*d*g^2+120*d*g+120 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

theorem qMoment_m51 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^5*X 1^1)=-720*d^6*g^5-2880*d^5*g^5-600*d^5*g^4-4320*d^4*g^5-1800*d^4*g^4-480*d^4*g^3-2880*d^3*g^5-1800*d^3*g^4-960*d^3*g^3-360*d^3*g^2-720*d^2*g^5-600*d^2*g^4-480*d^2*g^3-360*d^2*g^2-240*d^2*g-120*d+120 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

theorem qMoment_m60 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (X (0:Fin 2)^6*X 1^0)=720*d^6*g^6+3600*d^5*g^6+720*d^5*g^5+7200*d^4*g^6+2880*d^4*g^5+720*d^4*g^4+7200*d^3*g^6+4320*d^3*g^5+2160*d^3*g^4+720*d^3*g^3+3600*d^2*g^6+2880*d^2*g^5+2160*d^2*g^4+1440*d^2*g^3+720*d^2*g^2+720*d*g^6+720*d*g^5+720*d*g^4+720*d*g^3+720*d*g^2+720*d*g+720 := by
  rw [qMoment_monomial]
  norm_num [Finset.sum_range_succ,Nat.factorial,Nat.choose]
   <;> field_simp [show d+1≠0 by linarith]  <;> ring

def cov00 (d g:ℝ):ℝ := d^2*g^2+2*d*g^2+1
def cov01 (d g:ℝ):ℝ := -d^2*g-d*g
def cov11 (d g:ℝ):ℝ := d^2+1
def third0 (d g:ℝ):ℝ := 2*d^3*g^3+6*d^2*g^3+6*d*g^3+2
def third1 (d g:ℝ):ℝ := -2*d^3*g^2-4*d^2*g^2-2*d*g^2
def third2 (d g:ℝ):ℝ := 2*d^3*g+2*d^2*g
def third3 (d g:ℝ):ℝ := -2*d^3+2

def z0 (d g:ℝ):Poly := X 0-C (1+d*g)
def z1 (d g:ℝ):Poly := X 1-C (1-d)
def appell30 (d g:ℝ):Poly := z0 d g^3-C (3*cov00 d g)*z0 d g-C (third0 d g)
def appell21 (d g:ℝ):Poly := z0 d g^2*z1 d g-C (cov00 d g)*z1 d g-
  C (2*cov01 d g)*z0 d g-C (third1 d g)
def appell12 (d g:ℝ):Poly := z0 d g*z1 d g^2-C (cov11 d g)*z0 d g-
  C (2*cov01 d g)*z1 d g-C (third2 d g)
def appell03 (d g:ℝ):Poly := z1 d g^3-C (3*cov11 d g)*z1 d g-C (third3 d g)

theorem mean_z0 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (z0 d g)=0 := by
  have hp : (z0 d g)=
      C (1)*(X (0:Fin 2)^1*X 1^0)+
      C (-d*g-1)*(X (0:Fin 2)^0*X 1^0) := by
    simp only [z0,z1,cov00,cov01,cov11,third0,third1,third2,third3,appell30,appell21,appell12,appell03,map_add,map_mul,map_sub,map_neg,map_pow,map_natCast,map_ofNat,map_one,map_zero]
    ring
  rw [hp]
  simp only [qMoment_add,qMoment_C_mul,qMoment_m00 hd g,qMoment_m01 hd g,qMoment_m02 hd g,qMoment_m03 hd g,qMoment_m04 hd g,qMoment_m05 hd g,qMoment_m06 hd g,qMoment_m10 hd g,qMoment_m11 hd g,qMoment_m12 hd g,qMoment_m13 hd g,qMoment_m14 hd g,qMoment_m15 hd g,qMoment_m20 hd g,qMoment_m21 hd g,qMoment_m22 hd g,qMoment_m23 hd g,qMoment_m24 hd g,qMoment_m30 hd g,qMoment_m31 hd g,qMoment_m32 hd g,qMoment_m33 hd g,qMoment_m40 hd g,qMoment_m41 hd g,qMoment_m42 hd g,qMoment_m50 hd g,qMoment_m51 hd g,qMoment_m60 hd g]
  ring

theorem mean_z1 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (z1 d g)=0 := by
  have hp : (z1 d g)=
      C (1)*(X (0:Fin 2)^0*X 1^1)+
      C (d-1)*(X (0:Fin 2)^0*X 1^0) := by
    simp only [z0,z1,cov00,cov01,cov11,third0,third1,third2,third3,appell30,appell21,appell12,appell03,map_add,map_mul,map_sub,map_neg,map_pow,map_natCast,map_ofNat,map_one,map_zero]
    ring
  rw [hp]
  simp only [qMoment_add,qMoment_C_mul,qMoment_m00 hd g,qMoment_m01 hd g,qMoment_m02 hd g,qMoment_m03 hd g,qMoment_m04 hd g,qMoment_m05 hd g,qMoment_m06 hd g,qMoment_m10 hd g,qMoment_m11 hd g,qMoment_m12 hd g,qMoment_m13 hd g,qMoment_m14 hd g,qMoment_m15 hd g,qMoment_m20 hd g,qMoment_m21 hd g,qMoment_m22 hd g,qMoment_m23 hd g,qMoment_m24 hd g,qMoment_m30 hd g,qMoment_m31 hd g,qMoment_m32 hd g,qMoment_m33 hd g,qMoment_m40 hd g,qMoment_m41 hd g,qMoment_m42 hd g,qMoment_m50 hd g,qMoment_m51 hd g,qMoment_m60 hd g]
  ring

theorem second_z0 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (z0 d g*z0 d g)=cov00 d g := by
  have hp : (z0 d g*z0 d g)=
      C (1)*(X (0:Fin 2)^2*X 1^0)+
      C (-2*d*g-2)*(X (0:Fin 2)^1*X 1^0)+
      C (d^2*g^2+2*d*g+1)*(X (0:Fin 2)^0*X 1^0) := by
    simp only [z0,z1,cov00,cov01,cov11,third0,third1,third2,third3,appell30,appell21,appell12,appell03,map_add,map_mul,map_sub,map_neg,map_pow,map_natCast,map_ofNat,map_one,map_zero]
    ring
  rw [hp]
  simp only [qMoment_add,qMoment_C_mul,qMoment_m00 hd g,qMoment_m01 hd g,qMoment_m02 hd g,qMoment_m03 hd g,qMoment_m04 hd g,qMoment_m05 hd g,qMoment_m06 hd g,qMoment_m10 hd g,qMoment_m11 hd g,qMoment_m12 hd g,qMoment_m13 hd g,qMoment_m14 hd g,qMoment_m15 hd g,qMoment_m20 hd g,qMoment_m21 hd g,qMoment_m22 hd g,qMoment_m23 hd g,qMoment_m24 hd g,qMoment_m30 hd g,qMoment_m31 hd g,qMoment_m32 hd g,qMoment_m33 hd g,qMoment_m40 hd g,qMoment_m41 hd g,qMoment_m42 hd g,qMoment_m50 hd g,qMoment_m51 hd g,qMoment_m60 hd g]
  unfold cov00
  ring

theorem second_cross {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (z0 d g*z1 d g)=cov01 d g := by
  have hp : (z0 d g*z1 d g)=
      C (1)*(X (0:Fin 2)^1*X 1^1)+
      C (d-1)*(X (0:Fin 2)^1*X 1^0)+
      C (-d*g-1)*(X (0:Fin 2)^0*X 1^1)+
      C (-d^2*g+d*g-d+1)*(X (0:Fin 2)^0*X 1^0) := by
    simp only [z0,z1,cov00,cov01,cov11,third0,third1,third2,third3,appell30,appell21,appell12,appell03,map_add,map_mul,map_sub,map_neg,map_pow,map_natCast,map_ofNat,map_one,map_zero]
    ring
  rw [hp]
  simp only [qMoment_add,qMoment_C_mul,qMoment_m00 hd g,qMoment_m01 hd g,qMoment_m02 hd g,qMoment_m03 hd g,qMoment_m04 hd g,qMoment_m05 hd g,qMoment_m06 hd g,qMoment_m10 hd g,qMoment_m11 hd g,qMoment_m12 hd g,qMoment_m13 hd g,qMoment_m14 hd g,qMoment_m15 hd g,qMoment_m20 hd g,qMoment_m21 hd g,qMoment_m22 hd g,qMoment_m23 hd g,qMoment_m24 hd g,qMoment_m30 hd g,qMoment_m31 hd g,qMoment_m32 hd g,qMoment_m33 hd g,qMoment_m40 hd g,qMoment_m41 hd g,qMoment_m42 hd g,qMoment_m50 hd g,qMoment_m51 hd g,qMoment_m60 hd g]
  unfold cov01
  ring

theorem second_z1 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (z1 d g*z1 d g)=cov11 d g := by
  have hp : (z1 d g*z1 d g)=
      C (1)*(X (0:Fin 2)^0*X 1^2)+
      C (2*d-2)*(X (0:Fin 2)^0*X 1^1)+
      C (d^2-2*d+1)*(X (0:Fin 2)^0*X 1^0) := by
    simp only [z0,z1,cov00,cov01,cov11,third0,third1,third2,third3,appell30,appell21,appell12,appell03,map_add,map_mul,map_sub,map_neg,map_pow,map_natCast,map_ofNat,map_one,map_zero]
    ring
  rw [hp]
  simp only [qMoment_add,qMoment_C_mul,qMoment_m00 hd g,qMoment_m01 hd g,qMoment_m02 hd g,qMoment_m03 hd g,qMoment_m04 hd g,qMoment_m05 hd g,qMoment_m06 hd g,qMoment_m10 hd g,qMoment_m11 hd g,qMoment_m12 hd g,qMoment_m13 hd g,qMoment_m14 hd g,qMoment_m15 hd g,qMoment_m20 hd g,qMoment_m21 hd g,qMoment_m22 hd g,qMoment_m23 hd g,qMoment_m24 hd g,qMoment_m30 hd g,qMoment_m31 hd g,qMoment_m32 hd g,qMoment_m33 hd g,qMoment_m40 hd g,qMoment_m41 hd g,qMoment_m42 hd g,qMoment_m50 hd g,qMoment_m51 hd g,qMoment_m60 hd g]
  unfold cov11
  ring

theorem third_moment_0 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (z0 d g^3)=third0 d g := by
  have hp : (z0 d g^3)=
      C (1)*(X (0:Fin 2)^3*X 1^0)+
      C (-3*d*g-3)*(X (0:Fin 2)^2*X 1^0)+
      C (3*d^2*g^2+6*d*g+3)*(X (0:Fin 2)^1*X 1^0)+
      C (-d^3*g^3-3*d^2*g^2-3*d*g-1)*(X (0:Fin 2)^0*X 1^0) := by
    simp only [z0,z1,cov00,cov01,cov11,third0,third1,third2,third3,appell30,appell21,appell12,appell03,map_add,map_mul,map_sub,map_neg,map_pow,map_natCast,map_ofNat,map_one,map_zero]
    ring
  rw [hp]
  simp only [qMoment_add,qMoment_C_mul,qMoment_m00 hd g,qMoment_m01 hd g,qMoment_m02 hd g,qMoment_m03 hd g,qMoment_m04 hd g,qMoment_m05 hd g,qMoment_m06 hd g,qMoment_m10 hd g,qMoment_m11 hd g,qMoment_m12 hd g,qMoment_m13 hd g,qMoment_m14 hd g,qMoment_m15 hd g,qMoment_m20 hd g,qMoment_m21 hd g,qMoment_m22 hd g,qMoment_m23 hd g,qMoment_m24 hd g,qMoment_m30 hd g,qMoment_m31 hd g,qMoment_m32 hd g,qMoment_m33 hd g,qMoment_m40 hd g,qMoment_m41 hd g,qMoment_m42 hd g,qMoment_m50 hd g,qMoment_m51 hd g,qMoment_m60 hd g]
  unfold third0
  ring

theorem third_moment_1 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (z0 d g^2*z1 d g)=third1 d g := by
  have hp : (z0 d g^2*z1 d g)=
      C (1)*(X (0:Fin 2)^2*X 1^1)+
      C (d-1)*(X (0:Fin 2)^2*X 1^0)+
      C (-2*d*g-2)*(X (0:Fin 2)^1*X 1^1)+
      C (-2*d^2*g+2*d*g-2*d+2)*(X (0:Fin 2)^1*X 1^0)+
      C (d^2*g^2+2*d*g+1)*(X (0:Fin 2)^0*X 1^1)+
      C (d^3*g^2-d^2*g^2+2*d^2*g-2*d*g+d-1)*(X (0:Fin 2)^0*X 1^0) := by
    simp only [z0,z1,cov00,cov01,cov11,third0,third1,third2,third3,appell30,appell21,appell12,appell03,map_add,map_mul,map_sub,map_neg,map_pow,map_natCast,map_ofNat,map_one,map_zero]
    ring
  rw [hp]
  simp only [qMoment_add,qMoment_C_mul,qMoment_m00 hd g,qMoment_m01 hd g,qMoment_m02 hd g,qMoment_m03 hd g,qMoment_m04 hd g,qMoment_m05 hd g,qMoment_m06 hd g,qMoment_m10 hd g,qMoment_m11 hd g,qMoment_m12 hd g,qMoment_m13 hd g,qMoment_m14 hd g,qMoment_m15 hd g,qMoment_m20 hd g,qMoment_m21 hd g,qMoment_m22 hd g,qMoment_m23 hd g,qMoment_m24 hd g,qMoment_m30 hd g,qMoment_m31 hd g,qMoment_m32 hd g,qMoment_m33 hd g,qMoment_m40 hd g,qMoment_m41 hd g,qMoment_m42 hd g,qMoment_m50 hd g,qMoment_m51 hd g,qMoment_m60 hd g]
  unfold third1
  ring

theorem third_moment_2 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (z0 d g*z1 d g^2)=third2 d g := by
  have hp : (z0 d g*z1 d g^2)=
      C (1)*(X (0:Fin 2)^1*X 1^2)+
      C (2*d-2)*(X (0:Fin 2)^1*X 1^1)+
      C (d^2-2*d+1)*(X (0:Fin 2)^1*X 1^0)+
      C (-d*g-1)*(X (0:Fin 2)^0*X 1^2)+
      C (-2*d^2*g+2*d*g-2*d+2)*(X (0:Fin 2)^0*X 1^1)+
      C (-d^3*g+2*d^2*g-d^2-d*g+2*d-1)*(X (0:Fin 2)^0*X 1^0) := by
    simp only [z0,z1,cov00,cov01,cov11,third0,third1,third2,third3,appell30,appell21,appell12,appell03,map_add,map_mul,map_sub,map_neg,map_pow,map_natCast,map_ofNat,map_one,map_zero]
    ring
  rw [hp]
  simp only [qMoment_add,qMoment_C_mul,qMoment_m00 hd g,qMoment_m01 hd g,qMoment_m02 hd g,qMoment_m03 hd g,qMoment_m04 hd g,qMoment_m05 hd g,qMoment_m06 hd g,qMoment_m10 hd g,qMoment_m11 hd g,qMoment_m12 hd g,qMoment_m13 hd g,qMoment_m14 hd g,qMoment_m15 hd g,qMoment_m20 hd g,qMoment_m21 hd g,qMoment_m22 hd g,qMoment_m23 hd g,qMoment_m24 hd g,qMoment_m30 hd g,qMoment_m31 hd g,qMoment_m32 hd g,qMoment_m33 hd g,qMoment_m40 hd g,qMoment_m41 hd g,qMoment_m42 hd g,qMoment_m50 hd g,qMoment_m51 hd g,qMoment_m60 hd g]
  unfold third2
  ring

theorem third_moment_3 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (z1 d g^3)=third3 d g := by
  have hp : (z1 d g^3)=
      C (1)*(X (0:Fin 2)^0*X 1^3)+
      C (3*d-3)*(X (0:Fin 2)^0*X 1^2)+
      C (3*d^2-6*d+3)*(X (0:Fin 2)^0*X 1^1)+
      C (d^3-3*d^2+3*d-1)*(X (0:Fin 2)^0*X 1^0) := by
    simp only [z0,z1,cov00,cov01,cov11,third0,third1,third2,third3,appell30,appell21,appell12,appell03,map_add,map_mul,map_sub,map_neg,map_pow,map_natCast,map_ofNat,map_one,map_zero]
    ring
  rw [hp]
  simp only [qMoment_add,qMoment_C_mul,qMoment_m00 hd g,qMoment_m01 hd g,qMoment_m02 hd g,qMoment_m03 hd g,qMoment_m04 hd g,qMoment_m05 hd g,qMoment_m06 hd g,qMoment_m10 hd g,qMoment_m11 hd g,qMoment_m12 hd g,qMoment_m13 hd g,qMoment_m14 hd g,qMoment_m15 hd g,qMoment_m20 hd g,qMoment_m21 hd g,qMoment_m22 hd g,qMoment_m23 hd g,qMoment_m24 hd g,qMoment_m30 hd g,qMoment_m31 hd g,qMoment_m32 hd g,qMoment_m33 hd g,qMoment_m40 hd g,qMoment_m41 hd g,qMoment_m42 hd g,qMoment_m50 hd g,qMoment_m51 hd g,qMoment_m60 hd g]
  unfold third3
  ring

theorem mean_appell30 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (appell30 d g)=0 := by
  have hp : (appell30 d g)=
      C (1)*(X (0:Fin 2)^3*X 1^0)+
      C (-3*d*g-3)*(X (0:Fin 2)^2*X 1^0)+
      C (-6*d*g^2+6*d*g)*(X (0:Fin 2)^1*X 1^0)+
      C (-6*d*g^3+6*d*g^2)*(X (0:Fin 2)^0*X 1^0) := by
    simp only [z0,z1,cov00,cov01,cov11,third0,third1,third2,third3,appell30,appell21,appell12,appell03,map_add,map_mul,map_sub,map_neg,map_pow,map_natCast,map_ofNat,map_one,map_zero]
    ring
  rw [hp]
  simp only [qMoment_add,qMoment_C_mul,qMoment_m00 hd g,qMoment_m01 hd g,qMoment_m02 hd g,qMoment_m03 hd g,qMoment_m04 hd g,qMoment_m05 hd g,qMoment_m06 hd g,qMoment_m10 hd g,qMoment_m11 hd g,qMoment_m12 hd g,qMoment_m13 hd g,qMoment_m14 hd g,qMoment_m15 hd g,qMoment_m20 hd g,qMoment_m21 hd g,qMoment_m22 hd g,qMoment_m23 hd g,qMoment_m24 hd g,qMoment_m30 hd g,qMoment_m31 hd g,qMoment_m32 hd g,qMoment_m33 hd g,qMoment_m40 hd g,qMoment_m41 hd g,qMoment_m42 hd g,qMoment_m50 hd g,qMoment_m51 hd g,qMoment_m60 hd g]
  ring

theorem mean_appell21 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (appell21 d g)=0 := by
  have hp : (appell21 d g)=
      C (1)*(X (0:Fin 2)^2*X 1^1)+
      C (d-1)*(X (0:Fin 2)^2*X 1^0)+
      C (-2*d*g-2)*(X (0:Fin 2)^1*X 1^1)+
      C (4*d*g-2*d+2)*(X (0:Fin 2)^1*X 1^0)+
      C (-2*d*g^2+2*d*g)*(X (0:Fin 2)^0*X 1^1)+
      C (4*d*g^2-4*d*g)*(X (0:Fin 2)^0*X 1^0) := by
    simp only [z0,z1,cov00,cov01,cov11,third0,third1,third2,third3,appell30,appell21,appell12,appell03,map_add,map_mul,map_sub,map_neg,map_pow,map_natCast,map_ofNat,map_one,map_zero]
    ring
  rw [hp]
  simp only [qMoment_add,qMoment_C_mul,qMoment_m00 hd g,qMoment_m01 hd g,qMoment_m02 hd g,qMoment_m03 hd g,qMoment_m04 hd g,qMoment_m05 hd g,qMoment_m06 hd g,qMoment_m10 hd g,qMoment_m11 hd g,qMoment_m12 hd g,qMoment_m13 hd g,qMoment_m14 hd g,qMoment_m15 hd g,qMoment_m20 hd g,qMoment_m21 hd g,qMoment_m22 hd g,qMoment_m23 hd g,qMoment_m24 hd g,qMoment_m30 hd g,qMoment_m31 hd g,qMoment_m32 hd g,qMoment_m33 hd g,qMoment_m40 hd g,qMoment_m41 hd g,qMoment_m42 hd g,qMoment_m50 hd g,qMoment_m51 hd g,qMoment_m60 hd g]
  ring

theorem mean_appell12 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (appell12 d g)=0 := by
  have hp : (appell12 d g)=
      C (1)*(X (0:Fin 2)^1*X 1^2)+
      C (2*d-2)*(X (0:Fin 2)^1*X 1^1)+
      C (-2*d)*(X (0:Fin 2)^1*X 1^0)+
      C (-d*g-1)*(X (0:Fin 2)^0*X 1^2)+
      C (4*d*g-2*d+2)*(X (0:Fin 2)^0*X 1^1)+
      C (-2*d*g+2*d)*(X (0:Fin 2)^0*X 1^0) := by
    simp only [z0,z1,cov00,cov01,cov11,third0,third1,third2,third3,appell30,appell21,appell12,appell03,map_add,map_mul,map_sub,map_neg,map_pow,map_natCast,map_ofNat,map_one,map_zero]
    ring
  rw [hp]
  simp only [qMoment_add,qMoment_C_mul,qMoment_m00 hd g,qMoment_m01 hd g,qMoment_m02 hd g,qMoment_m03 hd g,qMoment_m04 hd g,qMoment_m05 hd g,qMoment_m06 hd g,qMoment_m10 hd g,qMoment_m11 hd g,qMoment_m12 hd g,qMoment_m13 hd g,qMoment_m14 hd g,qMoment_m15 hd g,qMoment_m20 hd g,qMoment_m21 hd g,qMoment_m22 hd g,qMoment_m23 hd g,qMoment_m24 hd g,qMoment_m30 hd g,qMoment_m31 hd g,qMoment_m32 hd g,qMoment_m33 hd g,qMoment_m40 hd g,qMoment_m41 hd g,qMoment_m42 hd g,qMoment_m50 hd g,qMoment_m51 hd g,qMoment_m60 hd g]
  ring

theorem mean_appell03 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (appell03 d g)=0 := by
  have hp : (appell03 d g)=
      C (1)*(X (0:Fin 2)^0*X 1^3)+
      C (3*d-3)*(X (0:Fin 2)^0*X 1^2)+
      C (-6*d)*(X (0:Fin 2)^0*X 1^1) := by
    simp only [z0,z1,cov00,cov01,cov11,third0,third1,third2,third3,appell30,appell21,appell12,appell03,map_add,map_mul,map_sub,map_neg,map_pow,map_natCast,map_ofNat,map_one,map_zero]
    ring
  rw [hp]
  simp only [qMoment_add,qMoment_C_mul,qMoment_m00 hd g,qMoment_m01 hd g,qMoment_m02 hd g,qMoment_m03 hd g,qMoment_m04 hd g,qMoment_m05 hd g,qMoment_m06 hd g,qMoment_m10 hd g,qMoment_m11 hd g,qMoment_m12 hd g,qMoment_m13 hd g,qMoment_m14 hd g,qMoment_m15 hd g,qMoment_m20 hd g,qMoment_m21 hd g,qMoment_m22 hd g,qMoment_m23 hd g,qMoment_m24 hd g,qMoment_m30 hd g,qMoment_m31 hd g,qMoment_m32 hd g,qMoment_m33 hd g,qMoment_m40 hd g,qMoment_m41 hd g,qMoment_m42 hd g,qMoment_m50 hd g,qMoment_m51 hd g,qMoment_m60 hd g]
  ring

def k00 (d g:ℝ):ℝ := 216*d^6*g^6+1296*d^5*g^6+3168*d^4*g^6+72*d^4*g^4+3960*d^3*g^6+288*d^3*g^4+72*d^3*g^3+2556*d^2*g^6+396*d^2*g^4+216*d^2*g^3+72*d^2*g^2+720*d*g^6+216*d*g^4+216*d*g^3+144*d*g^2+216

theorem gram_00 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (appell30 d g*appell30 d g)=216*d^6*g^6+1296*d^5*g^6+3168*d^4*g^6+72*d^4*g^4+3960*d^3*g^6+288*d^3*g^4+72*d^3*g^3+2556*d^2*g^6+396*d^2*g^4+216*d^2*g^3+72*d^2*g^2+720*d*g^6+216*d*g^4+216*d*g^3+144*d*g^2+216 := by
  have hp : (appell30 d g*appell30 d g)=
      C (1)*(X (0:Fin 2)^6*X 1^0)+
      C (-6*d*g-6)*(X (0:Fin 2)^5*X 1^0)+
      C (9*d^2*g^2-12*d*g^2+30*d*g+9)*(X (0:Fin 2)^4*X 1^0)+
      C (36*d^2*g^3-36*d^2*g^2-12*d*g^3+48*d*g^2-36*d*g)*(X (0:Fin 2)^3*X 1^0)+
      C (72*d^2*g^4-108*d^2*g^3+36*d^2*g^2+36*d*g^3-36*d*g^2)*(X (0:Fin 2)^2*X 1^0)+
      C (72*d^2*g^5-144*d^2*g^4+72*d^2*g^3)*(X (0:Fin 2)^1*X 1^0)+
      C (36*d^2*g^6-72*d^2*g^5+36*d^2*g^4)*(X (0:Fin 2)^0*X 1^0) := by
    simp only [z0,z1,cov00,cov01,cov11,third0,third1,third2,third3,appell30,appell21,appell12,appell03,map_add,map_mul,map_sub,map_neg,map_pow,map_natCast,map_ofNat,map_one,map_zero]
    ring
  rw [hp]
  simp only [qMoment_add,qMoment_C_mul,qMoment_m00 hd g,qMoment_m01 hd g,qMoment_m02 hd g,qMoment_m03 hd g,qMoment_m04 hd g,qMoment_m05 hd g,qMoment_m06 hd g,qMoment_m10 hd g,qMoment_m11 hd g,qMoment_m12 hd g,qMoment_m13 hd g,qMoment_m14 hd g,qMoment_m15 hd g,qMoment_m20 hd g,qMoment_m21 hd g,qMoment_m22 hd g,qMoment_m23 hd g,qMoment_m24 hd g,qMoment_m30 hd g,qMoment_m31 hd g,qMoment_m32 hd g,qMoment_m33 hd g,qMoment_m40 hd g,qMoment_m41 hd g,qMoment_m42 hd g,qMoment_m50 hd g,qMoment_m51 hd g,qMoment_m60 hd g]
  ring

theorem gram_k00 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (appell30 d g*appell30 d g)=k00 d g := gram_00 hd g

def k01 (d g:ℝ):ℝ := -216*d^6*g^5-1080*d^5*g^5-2112*d^4*g^5-48*d^4*g^3-1980*d^3*g^5-144*d^3*g^3-36*d^3*g^2-852*d^2*g^5-132*d^2*g^3-72*d^2*g^2-24*d^2*g-120*d*g^5-36*d*g^3-36*d*g^2-24*d*g

theorem gram_01 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (appell30 d g*appell21 d g)=-216*d^6*g^5-1080*d^5*g^5-2112*d^4*g^5-48*d^4*g^3-1980*d^3*g^5-144*d^3*g^3-36*d^3*g^2-852*d^2*g^5-132*d^2*g^3-72*d^2*g^2-24*d^2*g-120*d*g^5-36*d*g^3-36*d*g^2-24*d*g := by
  have hp : (appell30 d g*appell21 d g)=
      C (1)*(X (0:Fin 2)^5*X 1^1)+
      C (d-1)*(X (0:Fin 2)^5*X 1^0)+
      C (-5*d*g-5)*(X (0:Fin 2)^4*X 1^1)+
      C (-3*d^2*g+7*d*g-5*d+5)*(X (0:Fin 2)^4*X 1^0)+
      C (6*d^2*g^2-8*d*g^2+20*d*g+6)*(X (0:Fin 2)^3*X 1^1)+
      C (-18*d^2*g^2+12*d^2*g+10*d*g^2-28*d*g+6*d-6)*(X (0:Fin 2)^3*X 1^0)+
      C (18*d^2*g^3-18*d^2*g^2-6*d*g^3+24*d*g^2-18*d*g)*(X (0:Fin 2)^2*X 1^1)+
      C (-42*d^2*g^3+54*d^2*g^2-12*d^2*g+6*d*g^3-30*d*g^2+24*d*g)*(X (0:Fin 2)^2*X 1^0)+
      C (24*d^2*g^4-36*d^2*g^3+12*d^2*g^2+12*d*g^3-12*d*g^2)*(X (0:Fin 2)^1*X 1^1)+
      C (-48*d^2*g^4+84*d^2*g^3-36*d^2*g^2-12*d*g^3+12*d*g^2)*(X (0:Fin 2)^1*X 1^0)+
      C (12*d^2*g^5-24*d^2*g^4+12*d^2*g^3)*(X (0:Fin 2)^0*X 1^1)+
      C (-24*d^2*g^5+48*d^2*g^4-24*d^2*g^3)*(X (0:Fin 2)^0*X 1^0) := by
    simp only [z0,z1,cov00,cov01,cov11,third0,third1,third2,third3,appell30,appell21,appell12,appell03,map_add,map_mul,map_sub,map_neg,map_pow,map_natCast,map_ofNat,map_one,map_zero]
    ring
  rw [hp]
  simp only [qMoment_add,qMoment_C_mul,qMoment_m00 hd g,qMoment_m01 hd g,qMoment_m02 hd g,qMoment_m03 hd g,qMoment_m04 hd g,qMoment_m05 hd g,qMoment_m06 hd g,qMoment_m10 hd g,qMoment_m11 hd g,qMoment_m12 hd g,qMoment_m13 hd g,qMoment_m14 hd g,qMoment_m15 hd g,qMoment_m20 hd g,qMoment_m21 hd g,qMoment_m22 hd g,qMoment_m23 hd g,qMoment_m24 hd g,qMoment_m30 hd g,qMoment_m31 hd g,qMoment_m32 hd g,qMoment_m33 hd g,qMoment_m40 hd g,qMoment_m41 hd g,qMoment_m42 hd g,qMoment_m50 hd g,qMoment_m51 hd g,qMoment_m60 hd g]
  ring

theorem gram_k01 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (appell30 d g*appell21 d g)=k01 d g := gram_01 hd g

def k02 (d g:ℝ):ℝ := 216*d^6*g^4+864*d^5*g^4+1272*d^4*g^4+24*d^4*g^2+804*d^3*g^4+48*d^3*g^2+12*d^3*g+180*d^2*g^4+24*d^2*g^2+12*d^2*g

theorem gram_02 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (appell30 d g*appell12 d g)=216*d^6*g^4+864*d^5*g^4+1272*d^4*g^4+24*d^4*g^2+804*d^3*g^4+48*d^3*g^2+12*d^3*g+180*d^2*g^4+24*d^2*g^2+12*d^2*g := by
  have hp : (appell30 d g*appell12 d g)=
      C (1)*(X (0:Fin 2)^4*X 1^2)+
      C (2*d-2)*(X (0:Fin 2)^4*X 1^1)+
      C (-2*d)*(X (0:Fin 2)^4*X 1^0)+
      C (-4*d*g-4)*(X (0:Fin 2)^3*X 1^2)+
      C (-6*d^2*g+10*d*g-8*d+8)*(X (0:Fin 2)^3*X 1^1)+
      C (6*d^2*g-2*d*g+8*d)*(X (0:Fin 2)^3*X 1^0)+
      C (3*d^2*g^2-6*d*g^2+12*d*g+3)*(X (0:Fin 2)^2*X 1^2)+
      C (-24*d^2*g^2+18*d^2*g+12*d*g^2-30*d*g+6*d-6)*(X (0:Fin 2)^2*X 1^1)+
      C (18*d^2*g^2-18*d^2*g+6*d*g-6*d)*(X (0:Fin 2)^2*X 1^0)+
      C (6*d^2*g^3-6*d^2*g^2-6*d*g^3+12*d*g^2-6*d*g)*(X (0:Fin 2)^1*X 1^2)+
      C (-36*d^2*g^3+48*d^2*g^2-12*d^2*g+12*d*g^3-24*d*g^2+12*d*g)*(X (0:Fin 2)^1*X 1^1)+
      C (24*d^2*g^3-36*d^2*g^2+12*d^2*g)*(X (0:Fin 2)^1*X 1^0)+
      C (6*d^2*g^4-6*d^2*g^3+6*d*g^3-6*d*g^2)*(X (0:Fin 2)^0*X 1^2)+
      C (-24*d^2*g^4+36*d^2*g^3-12*d^2*g^2-12*d*g^3+12*d*g^2)*(X (0:Fin 2)^0*X 1^1)+
      C (12*d^2*g^4-24*d^2*g^3+12*d^2*g^2)*(X (0:Fin 2)^0*X 1^0) := by
    simp only [z0,z1,cov00,cov01,cov11,third0,third1,third2,third3,appell30,appell21,appell12,appell03,map_add,map_mul,map_sub,map_neg,map_pow,map_natCast,map_ofNat,map_one,map_zero]
    ring
  rw [hp]
  simp only [qMoment_add,qMoment_C_mul,qMoment_m00 hd g,qMoment_m01 hd g,qMoment_m02 hd g,qMoment_m03 hd g,qMoment_m04 hd g,qMoment_m05 hd g,qMoment_m06 hd g,qMoment_m10 hd g,qMoment_m11 hd g,qMoment_m12 hd g,qMoment_m13 hd g,qMoment_m14 hd g,qMoment_m15 hd g,qMoment_m20 hd g,qMoment_m21 hd g,qMoment_m22 hd g,qMoment_m23 hd g,qMoment_m24 hd g,qMoment_m30 hd g,qMoment_m31 hd g,qMoment_m32 hd g,qMoment_m33 hd g,qMoment_m40 hd g,qMoment_m41 hd g,qMoment_m42 hd g,qMoment_m50 hd g,qMoment_m51 hd g,qMoment_m60 hd g]
  ring

theorem gram_k02 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (appell30 d g*appell12 d g)=k02 d g := gram_02 hd g

def k03 (d g:ℝ):ℝ := -216*d^6*g^3-648*d^5*g^3-648*d^4*g^3-216*d^3*g^3

theorem gram_03 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (appell30 d g*appell03 d g)=-216*d^6*g^3-648*d^5*g^3-648*d^4*g^3-216*d^3*g^3 := by
  have hp : (appell30 d g*appell03 d g)=
      C (1)*(X (0:Fin 2)^3*X 1^3)+
      C (3*d-3)*(X (0:Fin 2)^3*X 1^2)+
      C (-6*d)*(X (0:Fin 2)^3*X 1^1)+
      C (-3*d*g-3)*(X (0:Fin 2)^2*X 1^3)+
      C (-9*d^2*g+9*d*g-9*d+9)*(X (0:Fin 2)^2*X 1^2)+
      C (18*d^2*g+18*d)*(X (0:Fin 2)^2*X 1^1)+
      C (-6*d*g^2+6*d*g)*(X (0:Fin 2)^1*X 1^3)+
      C (-18*d^2*g^2+18*d^2*g+18*d*g^2-18*d*g)*(X (0:Fin 2)^1*X 1^2)+
      C (36*d^2*g^2-36*d^2*g)*(X (0:Fin 2)^1*X 1^1)+
      C (-6*d*g^3+6*d*g^2)*(X (0:Fin 2)^0*X 1^3)+
      C (-18*d^2*g^3+18*d^2*g^2+18*d*g^3-18*d*g^2)*(X (0:Fin 2)^0*X 1^2)+
      C (36*d^2*g^3-36*d^2*g^2)*(X (0:Fin 2)^0*X 1^1) := by
    simp only [z0,z1,cov00,cov01,cov11,third0,third1,third2,third3,appell30,appell21,appell12,appell03,map_add,map_mul,map_sub,map_neg,map_pow,map_natCast,map_ofNat,map_one,map_zero]
    ring
  rw [hp]
  simp only [qMoment_add,qMoment_C_mul,qMoment_m00 hd g,qMoment_m01 hd g,qMoment_m02 hd g,qMoment_m03 hd g,qMoment_m04 hd g,qMoment_m05 hd g,qMoment_m06 hd g,qMoment_m10 hd g,qMoment_m11 hd g,qMoment_m12 hd g,qMoment_m13 hd g,qMoment_m14 hd g,qMoment_m15 hd g,qMoment_m20 hd g,qMoment_m21 hd g,qMoment_m22 hd g,qMoment_m23 hd g,qMoment_m24 hd g,qMoment_m30 hd g,qMoment_m31 hd g,qMoment_m32 hd g,qMoment_m33 hd g,qMoment_m40 hd g,qMoment_m41 hd g,qMoment_m42 hd g,qMoment_m50 hd g,qMoment_m51 hd g,qMoment_m60 hd g]
  ring

theorem gram_k03 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (appell30 d g*appell03 d g)=k03 d g := gram_03 hd g

def k11 (d g:ℝ):ℝ := 216*d^6*g^4+864*d^5*g^4+1272*d^4*g^4+32*d^4*g^2+816*d^3*g^4+64*d^3*g^2+16*d^3*g+208*d^2*g^4+32*d^2*g^2+16*d^2*g+8*d^2+24*d*g^4+8*d*g^2+8

theorem gram_11 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (appell21 d g*appell21 d g)=216*d^6*g^4+864*d^5*g^4+1272*d^4*g^4+32*d^4*g^2+816*d^3*g^4+64*d^3*g^2+16*d^3*g+208*d^2*g^4+32*d^2*g^2+16*d^2*g+8*d^2+24*d*g^4+8*d*g^2+8 := by
  have hp : (appell21 d g*appell21 d g)=
      C (1)*(X (0:Fin 2)^4*X 1^2)+
      C (2*d-2)*(X (0:Fin 2)^4*X 1^1)+
      C (d^2-2*d+1)*(X (0:Fin 2)^4*X 1^0)+
      C (-4*d*g-4)*(X (0:Fin 2)^3*X 1^2)+
      C (-4*d^2*g+12*d*g-8*d+8)*(X (0:Fin 2)^3*X 1^1)+
      C (8*d^2*g-4*d^2-8*d*g+8*d-4)*(X (0:Fin 2)^3*X 1^0)+
      C (4*d^2*g^2-4*d*g^2+12*d*g+4)*(X (0:Fin 2)^2*X 1^2)+
      C (-20*d^2*g^2+12*d^2*g+12*d*g^2-36*d*g+8*d-8)*(X (0:Fin 2)^2*X 1^1)+
      C (24*d^2*g^2-24*d^2*g+4*d^2-8*d*g^2+24*d*g-8*d+4)*(X (0:Fin 2)^2*X 1^0)+
      C (8*d^2*g^3-8*d^2*g^2+8*d*g^2-8*d*g)*(X (0:Fin 2)^1*X 1^2)+
      C (-32*d^2*g^3+40*d^2*g^2-8*d^2*g-24*d*g^2+24*d*g)*(X (0:Fin 2)^1*X 1^1)+
      C (32*d^2*g^3-48*d^2*g^2+16*d^2*g+16*d*g^2-16*d*g)*(X (0:Fin 2)^1*X 1^0)+
      C (4*d^2*g^4-8*d^2*g^3+4*d^2*g^2)*(X (0:Fin 2)^0*X 1^2)+
      C (-16*d^2*g^4+32*d^2*g^3-16*d^2*g^2)*(X (0:Fin 2)^0*X 1^1)+
      C (16*d^2*g^4-32*d^2*g^3+16*d^2*g^2)*(X (0:Fin 2)^0*X 1^0) := by
    simp only [z0,z1,cov00,cov01,cov11,third0,third1,third2,third3,appell30,appell21,appell12,appell03,map_add,map_mul,map_sub,map_neg,map_pow,map_natCast,map_ofNat,map_one,map_zero]
    ring
  rw [hp]
  simp only [qMoment_add,qMoment_C_mul,qMoment_m00 hd g,qMoment_m01 hd g,qMoment_m02 hd g,qMoment_m03 hd g,qMoment_m04 hd g,qMoment_m05 hd g,qMoment_m06 hd g,qMoment_m10 hd g,qMoment_m11 hd g,qMoment_m12 hd g,qMoment_m13 hd g,qMoment_m14 hd g,qMoment_m15 hd g,qMoment_m20 hd g,qMoment_m21 hd g,qMoment_m22 hd g,qMoment_m23 hd g,qMoment_m24 hd g,qMoment_m30 hd g,qMoment_m31 hd g,qMoment_m32 hd g,qMoment_m33 hd g,qMoment_m40 hd g,qMoment_m41 hd g,qMoment_m42 hd g,qMoment_m50 hd g,qMoment_m51 hd g,qMoment_m60 hd g]
  ring

theorem gram_k11 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (appell21 d g*appell21 d g)=k11 d g := gram_11 hd g

def k12 (d g:ℝ):ℝ := -216*d^6*g^3-648*d^5*g^3-648*d^4*g^3-16*d^4*g-240*d^3*g^3-16*d^3*g-4*d^3-32*d^2*g^3-4*d^2*g-4*d*g+4

theorem gram_12 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (appell21 d g*appell12 d g)=-216*d^6*g^3-648*d^5*g^3-648*d^4*g^3-16*d^4*g-240*d^3*g^3-16*d^3*g-4*d^3-32*d^2*g^3-4*d^2*g-4*d*g+4 := by
  have hp : (appell21 d g*appell12 d g)=
      C (1)*(X (0:Fin 2)^3*X 1^3)+
      C (3*d-3)*(X (0:Fin 2)^3*X 1^2)+
      C (2*d^2-6*d+2)*(X (0:Fin 2)^3*X 1^1)+
      C (-2*d^2+2*d)*(X (0:Fin 2)^3*X 1^0)+
      C (-3*d*g-3)*(X (0:Fin 2)^2*X 1^3)+
      C (-5*d^2*g+13*d*g-9*d+9)*(X (0:Fin 2)^2*X 1^2)+
      C (16*d^2*g-6*d^2-14*d*g+18*d-6)*(X (0:Fin 2)^2*X 1^1)+
      C (-10*d^2*g+6*d^2+2*d*g-6*d)*(X (0:Fin 2)^2*X 1^0)+
      C (2*d^2*g^2-2*d*g^2+6*d*g+2)*(X (0:Fin 2)^1*X 1^3)+
      C (-16*d^2*g^2+10*d^2*g+8*d*g^2-26*d*g+6*d-6)*(X (0:Fin 2)^1*X 1^2)+
      C (32*d^2*g^2-32*d^2*g+4*d^2-8*d*g^2+28*d*g-12*d+4)*(X (0:Fin 2)^1*X 1^1)+
      C (-16*d^2*g^2+20*d^2*g-4*d^2-4*d*g+4*d)*(X (0:Fin 2)^1*X 1^0)+
      C (2*d^2*g^3-2*d^2*g^2+2*d*g^2-2*d*g)*(X (0:Fin 2)^0*X 1^3)+
      C (-12*d^2*g^3+16*d^2*g^2-4*d^2*g-8*d*g^2+8*d*g)*(X (0:Fin 2)^0*X 1^2)+
      C (20*d^2*g^3-32*d^2*g^2+12*d^2*g+8*d*g^2-8*d*g)*(X (0:Fin 2)^0*X 1^1)+
      C (-8*d^2*g^3+16*d^2*g^2-8*d^2*g)*(X (0:Fin 2)^0*X 1^0) := by
    simp only [z0,z1,cov00,cov01,cov11,third0,third1,third2,third3,appell30,appell21,appell12,appell03,map_add,map_mul,map_sub,map_neg,map_pow,map_natCast,map_ofNat,map_one,map_zero]
    ring
  rw [hp]
  simp only [qMoment_add,qMoment_C_mul,qMoment_m00 hd g,qMoment_m01 hd g,qMoment_m02 hd g,qMoment_m03 hd g,qMoment_m04 hd g,qMoment_m05 hd g,qMoment_m06 hd g,qMoment_m10 hd g,qMoment_m11 hd g,qMoment_m12 hd g,qMoment_m13 hd g,qMoment_m14 hd g,qMoment_m15 hd g,qMoment_m20 hd g,qMoment_m21 hd g,qMoment_m22 hd g,qMoment_m23 hd g,qMoment_m24 hd g,qMoment_m30 hd g,qMoment_m31 hd g,qMoment_m32 hd g,qMoment_m33 hd g,qMoment_m40 hd g,qMoment_m41 hd g,qMoment_m42 hd g,qMoment_m50 hd g,qMoment_m51 hd g,qMoment_m60 hd g]
  ring

theorem gram_k12 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (appell21 d g*appell12 d g)=k12 d g := gram_12 hd g

def k13 (d g:ℝ):ℝ := 216*d^6*g^2+432*d^5*g^2+240*d^4*g^2+36*d^3*g^2-12*d*g^2

theorem gram_13 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (appell21 d g*appell03 d g)=216*d^6*g^2+432*d^5*g^2+240*d^4*g^2+36*d^3*g^2-12*d*g^2 := by
  have hp : (appell21 d g*appell03 d g)=
      C (1)*(X (0:Fin 2)^2*X 1^4)+
      C (4*d-4)*(X (0:Fin 2)^2*X 1^3)+
      C (3*d^2-12*d+3)*(X (0:Fin 2)^2*X 1^2)+
      C (-6*d^2+6*d)*(X (0:Fin 2)^2*X 1^1)+
      C (-2*d*g-2)*(X (0:Fin 2)^1*X 1^4)+
      C (-6*d^2*g+10*d*g-8*d+8)*(X (0:Fin 2)^1*X 1^3)+
      C (24*d^2*g-6*d^2-12*d*g+24*d-6)*(X (0:Fin 2)^1*X 1^2)+
      C (-24*d^2*g+12*d^2-12*d)*(X (0:Fin 2)^1*X 1^1)+
      C (-2*d*g^2+2*d*g)*(X (0:Fin 2)^0*X 1^4)+
      C (-6*d^2*g^2+6*d^2*g+10*d*g^2-10*d*g)*(X (0:Fin 2)^0*X 1^3)+
      C (24*d^2*g^2-24*d^2*g-12*d*g^2+12*d*g)*(X (0:Fin 2)^0*X 1^2)+
      C (-24*d^2*g^2+24*d^2*g)*(X (0:Fin 2)^0*X 1^1) := by
    simp only [z0,z1,cov00,cov01,cov11,third0,third1,third2,third3,appell30,appell21,appell12,appell03,map_add,map_mul,map_sub,map_neg,map_pow,map_natCast,map_ofNat,map_one,map_zero]
    ring
  rw [hp]
  simp only [qMoment_add,qMoment_C_mul,qMoment_m00 hd g,qMoment_m01 hd g,qMoment_m02 hd g,qMoment_m03 hd g,qMoment_m04 hd g,qMoment_m05 hd g,qMoment_m06 hd g,qMoment_m10 hd g,qMoment_m11 hd g,qMoment_m12 hd g,qMoment_m13 hd g,qMoment_m14 hd g,qMoment_m15 hd g,qMoment_m20 hd g,qMoment_m21 hd g,qMoment_m22 hd g,qMoment_m23 hd g,qMoment_m24 hd g,qMoment_m30 hd g,qMoment_m31 hd g,qMoment_m32 hd g,qMoment_m33 hd g,qMoment_m40 hd g,qMoment_m41 hd g,qMoment_m42 hd g,qMoment_m50 hd g,qMoment_m51 hd g,qMoment_m60 hd g]
  ring

theorem gram_k13 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (appell21 d g*appell03 d g)=k13 d g := gram_13 hd g

def k22 (d g:ℝ):ℝ := 216*d^6*g^2+432*d^5*g^2+240*d^4*g^2+8*d^4+48*d^3*g^2+4*d^2*g^2+4*d^2+8

theorem gram_22 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (appell12 d g*appell12 d g)=216*d^6*g^2+432*d^5*g^2+240*d^4*g^2+8*d^4+48*d^3*g^2+4*d^2*g^2+4*d^2+8 := by
  have hp : (appell12 d g*appell12 d g)=
      C (1)*(X (0:Fin 2)^2*X 1^4)+
      C (4*d-4)*(X (0:Fin 2)^2*X 1^3)+
      C (4*d^2-12*d+4)*(X (0:Fin 2)^2*X 1^2)+
      C (-8*d^2+8*d)*(X (0:Fin 2)^2*X 1^1)+
      C (4*d^2)*(X (0:Fin 2)^2*X 1^0)+
      C (-2*d*g-2)*(X (0:Fin 2)^1*X 1^4)+
      C (-4*d^2*g+12*d*g-8*d+8)*(X (0:Fin 2)^1*X 1^3)+
      C (20*d^2*g-8*d^2-20*d*g+24*d-8)*(X (0:Fin 2)^1*X 1^2)+
      C (-24*d^2*g+16*d^2+8*d*g-16*d)*(X (0:Fin 2)^1*X 1^1)+
      C (8*d^2*g-8*d^2)*(X (0:Fin 2)^1*X 1^0)+
      C (d^2*g^2+2*d*g+1)*(X (0:Fin 2)^0*X 1^4)+
      C (-8*d^2*g^2+4*d^2*g-12*d*g+4*d-4)*(X (0:Fin 2)^0*X 1^3)+
      C (20*d^2*g^2-20*d^2*g+4*d^2+20*d*g-12*d+4)*(X (0:Fin 2)^0*X 1^2)+
      C (-16*d^2*g^2+24*d^2*g-8*d^2-8*d*g+8*d)*(X (0:Fin 2)^0*X 1^1)+
      C (4*d^2*g^2-8*d^2*g+4*d^2)*(X (0:Fin 2)^0*X 1^0) := by
    simp only [z0,z1,cov00,cov01,cov11,third0,third1,third2,third3,appell30,appell21,appell12,appell03,map_add,map_mul,map_sub,map_neg,map_pow,map_natCast,map_ofNat,map_one,map_zero]
    ring
  rw [hp]
  simp only [qMoment_add,qMoment_C_mul,qMoment_m00 hd g,qMoment_m01 hd g,qMoment_m02 hd g,qMoment_m03 hd g,qMoment_m04 hd g,qMoment_m05 hd g,qMoment_m06 hd g,qMoment_m10 hd g,qMoment_m11 hd g,qMoment_m12 hd g,qMoment_m13 hd g,qMoment_m14 hd g,qMoment_m15 hd g,qMoment_m20 hd g,qMoment_m21 hd g,qMoment_m22 hd g,qMoment_m23 hd g,qMoment_m24 hd g,qMoment_m30 hd g,qMoment_m31 hd g,qMoment_m32 hd g,qMoment_m33 hd g,qMoment_m40 hd g,qMoment_m41 hd g,qMoment_m42 hd g,qMoment_m50 hd g,qMoment_m51 hd g,qMoment_m60 hd g]
  ring

theorem gram_k22 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (appell12 d g*appell12 d g)=k22 d g := gram_22 hd g

def k23 (d g:ℝ):ℝ := -216*d^6*g-216*d^5*g-48*d^4*g-12*d^3*g+12*d^2*g-24*d*g

theorem gram_23 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (appell12 d g*appell03 d g)=-216*d^6*g-216*d^5*g-48*d^4*g-12*d^3*g+12*d^2*g-24*d*g := by
  have hp : (appell12 d g*appell03 d g)=
      C (1)*(X (0:Fin 2)^1*X 1^5)+
      C (5*d-5)*(X (0:Fin 2)^1*X 1^4)+
      C (6*d^2-20*d+6)*(X (0:Fin 2)^1*X 1^3)+
      C (-18*d^2+18*d)*(X (0:Fin 2)^1*X 1^2)+
      C (12*d^2)*(X (0:Fin 2)^1*X 1^1)+
      C (-d*g-1)*(X (0:Fin 2)^0*X 1^5)+
      C (-3*d^2*g+7*d*g-5*d+5)*(X (0:Fin 2)^0*X 1^4)+
      C (18*d^2*g-6*d^2-14*d*g+20*d-6)*(X (0:Fin 2)^0*X 1^3)+
      C (-30*d^2*g+18*d^2+6*d*g-18*d)*(X (0:Fin 2)^0*X 1^2)+
      C (12*d^2*g-12*d^2)*(X (0:Fin 2)^0*X 1^1) := by
    simp only [z0,z1,cov00,cov01,cov11,third0,third1,third2,third3,appell30,appell21,appell12,appell03,map_add,map_mul,map_sub,map_neg,map_pow,map_natCast,map_ofNat,map_one,map_zero]
    ring
  rw [hp]
  simp only [qMoment_add,qMoment_C_mul,qMoment_m00 hd g,qMoment_m01 hd g,qMoment_m02 hd g,qMoment_m03 hd g,qMoment_m04 hd g,qMoment_m05 hd g,qMoment_m06 hd g,qMoment_m10 hd g,qMoment_m11 hd g,qMoment_m12 hd g,qMoment_m13 hd g,qMoment_m14 hd g,qMoment_m15 hd g,qMoment_m20 hd g,qMoment_m21 hd g,qMoment_m22 hd g,qMoment_m23 hd g,qMoment_m24 hd g,qMoment_m30 hd g,qMoment_m31 hd g,qMoment_m32 hd g,qMoment_m33 hd g,qMoment_m40 hd g,qMoment_m41 hd g,qMoment_m42 hd g,qMoment_m50 hd g,qMoment_m51 hd g,qMoment_m60 hd g]
  ring

theorem gram_k23 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (appell12 d g*appell03 d g)=k23 d g := gram_23 hd g

def k33 (d g:ℝ):ℝ := 216*d^6+72*d^4-72*d^3+72*d^2+216

theorem gram_33 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (appell03 d g*appell03 d g)=216*d^6+72*d^4-72*d^3+72*d^2+216 := by
  have hp : (appell03 d g*appell03 d g)=
      C (1)*(X (0:Fin 2)^0*X 1^6)+
      C (6*d-6)*(X (0:Fin 2)^0*X 1^5)+
      C (9*d^2-30*d+9)*(X (0:Fin 2)^0*X 1^4)+
      C (-36*d^2+36*d)*(X (0:Fin 2)^0*X 1^3)+
      C (36*d^2)*(X (0:Fin 2)^0*X 1^2) := by
    simp only [z0,z1,cov00,cov01,cov11,third0,third1,third2,third3,appell30,appell21,appell12,appell03,map_add,map_mul,map_sub,map_neg,map_pow,map_natCast,map_ofNat,map_one,map_zero]
    ring
  rw [hp]
  simp only [qMoment_add,qMoment_C_mul,qMoment_m00 hd g,qMoment_m01 hd g,qMoment_m02 hd g,qMoment_m03 hd g,qMoment_m04 hd g,qMoment_m05 hd g,qMoment_m06 hd g,qMoment_m10 hd g,qMoment_m11 hd g,qMoment_m12 hd g,qMoment_m13 hd g,qMoment_m14 hd g,qMoment_m15 hd g,qMoment_m20 hd g,qMoment_m21 hd g,qMoment_m22 hd g,qMoment_m23 hd g,qMoment_m24 hd g,qMoment_m30 hd g,qMoment_m31 hd g,qMoment_m32 hd g,qMoment_m33 hd g,qMoment_m40 hd g,qMoment_m41 hd g,qMoment_m42 hd g,qMoment_m50 hd g,qMoment_m51 hd g,qMoment_m60 hd g]
  ring

theorem gram_k33 {d:ℝ} (hd:0 ≤ d) (g:ℝ):
    qMoment d g (appell03 d g*appell03 d g)=k33 d g := gram_33 hd g

def cubicPolynomial (d g x y z w:ℝ):Poly :=
  C x*appell30 d g+C y*appell21 d g+C z*appell12 d g+C w*appell03 d g

def gramQuadratic (d g x y z w:ℝ):ℝ :=
  quadratic (k00 d g) (k11 d g) (k22 d g) (k33 d g)
    (k01 d g) (k02 d g) (k03 d g) (k12 d g) (k13 d g) (k23 d g) x y z w

def covarianceTensorQuadratic (d g x y z w:ℝ):ℝ :=
  quadratic (cov00 d g^3)
    ((cov00 d g^2*cov11 d g+2*cov00 d g*cov01 d g^2)/3)
    ((cov00 d g*cov11 d g^2+2*cov01 d g^2*cov11 d g)/3) (cov11 d g^3)
    (cov00 d g^2*cov01 d g) (cov00 d g*cov01 d g^2) (cov01 d g^3)
    ((cov01 d g^3+2*cov00 d g*cov01 d g*cov11 d g)/3)
    (cov01 d g^2*cov11 d g) (cov01 d g*cov11 d g^2) x y z w

theorem qMoment_cubicPolynomial_sq {d:ℝ} (hd:0 ≤ d) (g x y z w:ℝ):
    qMoment d g (cubicPolynomial d g x y z w^2)=gramQuadratic d g x y z w := by
  have hp : cubicPolynomial d g x y z w^2=
      C (x^2)*(appell30 d g*appell30 d g)+
      C (2*x*y)*(appell30 d g*appell21 d g)+
      C (2*x*z)*(appell30 d g*appell12 d g)+
      C (2*x*w)*(appell30 d g*appell03 d g)+
      C (y^2)*(appell21 d g*appell21 d g)+
      C (2*y*z)*(appell21 d g*appell12 d g)+
      C (2*y*w)*(appell21 d g*appell03 d g)+
      C (z^2)*(appell12 d g*appell12 d g)+
      C (2*z*w)*(appell12 d g*appell03 d g)+
      C (w^2)*(appell03 d g*appell03 d g) := by
    simp only [cubicPolynomial,map_mul,map_pow,map_ofNat]
    ring
  rw [hp]
  simp only [qMoment_add,qMoment_C_mul,gram_k00 hd g,gram_k01 hd g,gram_k02 hd g,gram_k03 hd g,gram_k11 hd g,gram_k12 hd g,gram_k13 hd g,gram_k22 hd g,gram_k23 hd g,gram_k33 hd g]
  unfold gramQuadratic quadratic
  ring

theorem slack_connection (d g x y z w:ℝ):
    slackQuadratic d g x y z w=
      216*covarianceTensorQuadratic d g x y z w-gramQuadratic d g x y z w := by
  unfold slackQuadratic covarianceTensorQuadratic gramQuadratic quadratic
    cov00 cov01 cov11 m00 m01 m02 m03 m11 m12 m13 m22 m23 m33
    k00 k01 k02 k03 k11 k12 k13 k22 k23 k33
  ring

theorem actual_cubic_covariance_cap {d g:ℝ} (hd:0  <  d) (hg:0 ≤ g) (hg1:g ≤ 1)
    (x y z w:ℝ):
    (∫u,polyEval (cubicPolynomial d g x y z w) u^2 ∂rawMeasure d g) ≤ 
      216*covarianceTensorQuadratic d g x y z w := by
  have he : (fun u:Space 2=>polyEval (cubicPolynomial d g x y z w) u^2)=
      (fun u=>polyEval (cubicPolynomial d g x y z w^2) u) := by
    funext u
    simp only [polyEval,MvPolynomial.eval_pow]
  rw [he]
  change rawMoment d g (cubicPolynomial d g x y z w^2) ≤ _
  rw [rawMoment_eq_qMoment hd.le,qMoment_cubicPolynomial_sq hd.le]
  have h:=slackQuadratic_nonneg hd hg hg1 x y z w
  rw [slack_connection] at h
  linarith

end KLSImprovement.TwoConeActualCubic
#print axioms KLSImprovement.TwoConeActualCubic.mean_z0
#print axioms KLSImprovement.TwoConeActualCubic.second_cross
#print axioms KLSImprovement.TwoConeActualCubic.third_moment_1
#print axioms KLSImprovement.TwoConeActualCubic.gram_k12
#print axioms KLSImprovement.TwoConeActualCubic.actual_cubic_covariance_cap

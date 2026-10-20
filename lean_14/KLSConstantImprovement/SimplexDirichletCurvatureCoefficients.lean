import KLSConstantImprovement.GammaRadialCurvatureCoefficients
import KLSConstantImprovement.DeficitCurvatureScalar

/-! Exact positive polynomial certificate for every real m>=2 and the
complete scalar Dirichlet matrix interpolation for 0 < =x<=1.
Actual law moment/tensor identifications are separate from this module. -/
noncomputable section
namespace KLSConstantImprovement.SimplexDirichletCurvatureCoefficients
open GammaRadialCurvatureCoefficients
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
def b (m : ℝ) := m*(m+1)/((m+2)*(m+3))
def c (m : ℝ) := m^2*(m+1)^2/((m+2)*(m+3)*(m+4)*(m+5))
def r (m : ℝ) := 4*m*(m+1)/(m+2)^2
def delta (m : ℝ) := (m+2)^2*(m+3)*(m+4)*(m+5)
def nu (m : ℝ) := 180-12*b m-6*c m
def diag (m : ℝ) := 180-48*b m+21*r m-216*c m
def alpha (m : ℝ) := 12*b m-3-9*c m
def epsilon (m : ℝ) := r m-4*c m
def off (m : ℝ) := 540-72*b m-21*r m-36*c m
def ell (m : ℝ) := 18*(b m-c m)
def u0 (m : ℝ) := -36*b m-54*c m
def s0 (m : ℝ) := 21*r m-36*c m
def poly_nu (h : ℝ) : ℝ := 591840+h*(592056+h*(233592+h*(45378+h*(4332+h*(162)))))
def poly_d (h : ℝ) : ℝ := 631152+h*(625680+h*(234924+h*(39600+h*(2532))))
def poly_alpha (h : ℝ) : ℝ := 720+h*(4188+h*(2946+h*(726+h*(60))))
def poly_epsilon (h : ℝ) : ℝ := 4464+h*(5664+h*(2580+h*(504+h*(36))))
def poly_off (h : ℝ) : ℝ := 1630800+h*(1578528+h*(598740+h*(111036+h*(10020+h*(348)))))
def poly_determinant (h : ℝ) : ℝ := 212564736+h*(2462218560+h*(3938762592+h*(2864514960+h*(1176746040+h*(292282200+h*(43767288+h*(3654360+h*(131184))))))))

theorem polynomial_rows_positive {h : ℝ} (hh : 0 ≤ h) :
    0 < poly_nu h ∧ 0 < poly_d h ∧ 0 < poly_alpha h ∧ 0 < poly_epsilon h ∧
      0 < poly_off h ∧ 0 < poly_determinant h := by
  unfold poly_nu poly_d poly_alpha poly_epsilon poly_off poly_determinant
  exact ⟨by positivity,by positivity,by positivity,by positivity,by positivity,by positivity⟩

theorem delta_positive {m : ℝ} (hm : 2 ≤ m) : 0 < delta m := by
  unfold delta
  have h2:0 < m+2 := by linarith
  have h3:0 < m+3 := by linarith
  have h4:0 < m+4 := by linarith
  have h5:0 < m+5 := by linarith
  positivity

theorem cleared_coefficients {m : ℝ} (hm : 2 ≤ m) :
    delta m*nu m=poly_nu (m-2) ∧ delta m*diag m=poly_d (m-2) ∧
    delta m*alpha m=poly_alpha (m-2) ∧ delta m*epsilon m=poly_epsilon (m-2) ∧
    delta m*off m=poly_off (m-2) ∧
    (delta m)^2*(diag m*alpha m-(ell m)^2)=poly_determinant (m-2) := by
  have h2:m+2 ≠ 0 := ne_of_gt (by linarith)
  have h3:m+3 ≠ 0 := ne_of_gt (by linarith)
  have h4:m+4 ≠ 0 := ne_of_gt (by linarith)
  have h5:m+5 ≠ 0 := ne_of_gt (by linarith)
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;>
    simp only [delta,nu,diag,alpha,epsilon,off,ell,b,c,r,poly_nu,poly_d,poly_alpha,
      poly_epsilon,poly_off,poly_determinant] <;> field_simp [h2,h3,h4,h5] <;>ring

theorem coefficients_positive {m : ℝ} (hm : 2 ≤ m) :
    0 < nu m ∧ 0 < diag m ∧ 0 < alpha m ∧ 0 < epsilon m ∧ 0 < off m ∧
      0 < diag m*alpha m-(ell m)^2 := by
  rcases cleared_coefficients hm with ⟨h1,h2,h3,h4,h5,h6⟩
  rcases polynomial_rows_positive (show 0 ≤ m-2 by linarith) with ⟨p1,p2,p3,p4,p5,p6⟩
  have hD:=delta_positive hm
  have hD2:=pow_pos hD 2
  exact ⟨(mul_pos_iff_of_pos_left hD).mp (h1.symm ▸ p1),
    (mul_pos_iff_of_pos_left hD).mp (h2.symm ▸ p2),
    (mul_pos_iff_of_pos_left hD).mp (h3.symm ▸ p3),
    (mul_pos_iff_of_pos_left hD).mp (h4.symm ▸ p4),
    (mul_pos_iff_of_pos_left hD).mp (h5.symm ▸ p5),
    (mul_pos_iff_of_pos_left hD2).mp (h6.symm ▸ p6)⟩

theorem simplex_matrix_positive {m z t : ℝ} (hm : 2 ≤ m) (hne : z ≠ 0 ∨ t ≠ 0) :
    0 < quadratic (diag m) (ell m) (alpha m) z t :=
  quadratic_positive (coefficients_positive hm).2.1 (coefficients_positive hm).2.2.2.2.2 hne

theorem radial_coefficients_positive {m : ℝ} (hm : 2 ≤ m) : 0 < b m ∧ 0 < c m ∧ 0 < r m := by
  have hm0:0 < m := by linarith
  have h1:0 < m+1 := by linarith
  have h2:0 < m+2 := by linarith
  have h3:0 < m+3 := by linarith
  have h4:0 < m+4 := by linarith
  have h5:0 < m+5 := by linarith
  unfold b c r
  exact ⟨by positivity,by positivity,by positivity⟩

def interpolationForm (m x z t : ℝ) : ℝ :=
  (nu m+(u0 m+s0 m)*x-120*c m*x^2)*z^2+2*ell m*x*z*t+alpha m*t^2

theorem interpolation_sos (m x z t : ℝ) :
    interpolationForm m x z t=(1-x)*(nu m*z^2+alpha m*t^2)+
      x*quadratic (diag m) (ell m) (alpha m) z t+120*c m*x*(1-x)*z^2 := by
  unfold interpolationForm quadratic nu diag alpha u0 s0
  ring

theorem interpolation_positive {m x z t : ℝ} (hm : 2 ≤ m) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hne : z ≠ 0 ∨ t ≠ 0) : 0 < interpolationForm m x z t := by
  have hp:=coefficients_positive hm
  have hdiag:0 < nu m*z^2+alpha m*t^2 := by
    have h:=quadratic_positive hp.1
      (show 0 < nu m*alpha m-(0:ℝ)^2 by simpa using mul_pos hp.1 hp.2.2.1) hne
    simpa only [quadratic,mul_zero,zero_mul,add_zero] using h
  have hquad:=simplex_matrix_positive hm hne
  have hrest:0 ≤ 120*c m*x*(1-x)*z^2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (radial_coefficients_positive hm).2.1.le) hx) (by linarith)) (sq_nonneg _)
  rw [interpolation_sos]
  by_cases hz:x=0
  · simp only [hz,sub_zero,mul_zero,zero_mul,add_zero,one_mul]
    exact hdiag
  · have hxp:0 < x := lt_of_le_of_ne hx (Ne.symm hz)
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) hdiag.le) (mul_pos hxp hquad)) hrest

theorem off_interpolation_lower {m x : ℝ} (hm : 2 ≤ m) (hx1 : x ≤ 1) :
    off m ≤ 3*nu m+(u0 m-s0 m)*x := by
  have hr:=radial_coefficients_positive hm
  have hsgn:u0 m-s0 m ≤ 0 := by unfold u0 s0;linarith [hr.1,hr.2.1,hr.2.2]
  have h:=mul_le_mul_of_nonpos_left hx1 hsgn
  unfold off nu u0 s0 at *
  nlinarith

theorem curvature_twenty_seven_gives_cubic260 {J V F S N : ℝ}
    (hid : J+V=21*F+21*S+6*N) (hcurv : -(27:ℝ)*(6*N-F) ≤ J)
    (hBessel : S ≤ F+2*N) (hS : S ≤ (16/3:ℝ)*N) : V ≤ 260*N := by
  have hc:=DeficitCurvatureScalar.curvature_conversion hid hcurv
  by_cases hF:F ≤ (10/3:ℝ)*N <;>nlinarith

end KLSConstantImprovement.SimplexDirichletCurvatureCoefficients
#print axioms KLSConstantImprovement.SimplexDirichletCurvatureCoefficients.cleared_coefficients
#print axioms KLSConstantImprovement.SimplexDirichletCurvatureCoefficients.coefficients_positive
#print axioms KLSConstantImprovement.SimplexDirichletCurvatureCoefficients.simplex_matrix_positive
#print axioms KLSConstantImprovement.SimplexDirichletCurvatureCoefficients.interpolation_positive
#print axioms KLSConstantImprovement.SimplexDirichletCurvatureCoefficients.off_interpolation_lower
#print axioms KLSConstantImprovement.SimplexDirichletCurvatureCoefficients.curvature_twenty_seven_gives_cubic260

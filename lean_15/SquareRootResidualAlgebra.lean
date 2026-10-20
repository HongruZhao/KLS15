import VariableAlpha24Numerics

/-! Exact scalar square-root and variable-alpha residual algebra. -/
noncomputable section
namespace VariableAlpha24
set_option maxHeartbeats 2000000

 theorem sqrt_residual_positive {z P Q : ℝ} (hz : 0<z)
    (hP : 0<P) (hQ : 0<Q) (hd : 0<P^2-z*Q^2) :
    0<P-Real.sqrt z*Q := by
  have hs : 0 ≤ Real.sqrt z*Q := mul_nonneg (Real.sqrt_nonneg z) hQ.le
  have he : (Real.sqrt z*Q)^2=z*Q^2 := by rw [mul_pow,Real.sq_sqrt hz.le]
  have hh : (Real.sqrt z*Q)^2<P^2 := by rw [he]; linarith
  have hh' := (sq_lt_sq₀ hs hP.le).mp hh
  linarith

 theorem alpha_mem_unit_of_polynomial {z c t v : ℝ} (hz : 0<z)
    (hc : 0<c) (ht : 0<t) (hv : 0<v)
    (ha : 0<z-c^2*t^2*v^2) :
    1-c*t*v/Real.sqrt z∈Set.Ioo (0:ℝ) 1 := by
  have hp : 0<c*t*v := by positivity
  have hs : 0<Real.sqrt z := Real.sqrt_pos.mpr hz
  have hsq : (c*t*v)^2<(Real.sqrt z)^2 := by rw [Real.sq_sqrt hz.le]; nlinarith
  have hlt := (sq_lt_sq₀ hp.le hs.le).mp hsq
  have hd : c*t*v/Real.sqrt z<1 := (div_lt_one hs).mpr hlt
  have hd0 : 0<c*t*v/Real.sqrt z := div_pos hp hs
  constructor <;> linarith

 theorem variable_alpha_residual_identity {z c t v s p C D R r0 a : ℝ}
    (hz : 0<z) (hc : c≠0) (ht : t≠0) (hv : v≠0) :
    let alpha := 1-c*t*v/Real.sqrt z
    alpha*p*z-(C/(1-alpha)-D)*(t^2*v^2)-r0*t*v+
      (a*z+R*Real.sqrt z)*(-v*s) =
      (-a*z*v*s+p*z+D*t^2*v^2-r0*t*v)-
        Real.sqrt z*(R*v*s+(p*c+C/c)*t*v) := by
  dsimp only
  have hs : Real.sqrt z≠0 := ne_of_gt (Real.sqrt_pos.mpr hz)
  have hsdiv : z/Real.sqrt z=Real.sqrt z := by
    apply (div_eq_iff hs).mpr
    nlinarith [Real.sq_sqrt hz.le]
  have he1 : (1-c*t*v/Real.sqrt z)*p*z=p*z-c*p*t*v*Real.sqrt z := by
    calc
      _=p*z-c*p*t*v*(z/Real.sqrt z) := by ring
      _=_ := by rw [hsdiv]
  have he2 : (C/(1-(1-c*t*v/Real.sqrt z))-D)*(t^2*v^2)=
      (C/c)*t*v*Real.sqrt z-D*t^2*v^2 := by
    field_simp
    <;> ring
  rw [he1,he2]
  ring

 theorem parameterized_z_positive {t T : ℝ} (ht : 0≤t) (htT : t≤T) (hT : T<1) :
    0<1-t^2 := by
  have hlt : t<1 := lt_of_le_of_lt htT hT
  have hm : 0<(1-t)*(1+t) := mul_pos (by linarith) (by linarith)
  nlinarith

end VariableAlpha24
#print axioms VariableAlpha24.sqrt_residual_positive
#print axioms VariableAlpha24.variable_alpha_residual_identity

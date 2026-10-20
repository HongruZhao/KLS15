import NormalizedProjectionOrbitRecurrence
noncomputable section
open InnerProductSpace ContinuousLinearMap AdjointOrbitRecurrence
namespace KLSBelow25.ProjectionOrbitSlack
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem normalized_projection_energy_recurrence (R P : H→L[ℝ]H) (f : H)
    {K : ℝ} (hK : 0<K)
    (hcomp : ∀ v, ‖R v‖^2≤‖R.adjoint v‖^2+‖P v‖^2)
    (m : ℕ) (_hm : 0<normalizedOrbit R f K m)
    (hm1 : 0<normalizedOrbit R f K (m+1)) :
    (normalizedOrbit R f K (m+1))^2/normalizedOrbit R f K m-
      ‖P (orbit R f (m+1))‖^2/K^(m+2)≤normalizedOrbit R f K (m+2) := by
  have hh := shifted_ratio_recurrence R P f hK m
  have ha := shifted_slack_nonneg R P f hK hcomp m
  rw [shifted_ratio_eq_normalized R f hK (m+1),
    shifted_ratio_eq_normalized R f hK m,
    shifted_observation_eq_normalized R P f hK m,
    show m+1+1=m+2 by omega] at hh
  have ht : normalizedOrbit R f K (m+1)/normalizedOrbit R f K m-
      (‖P (orbit R f (m+1))‖^2/K^(m+2))/normalizedOrbit R f K (m+1)≤
      normalizedOrbit R f K (m+2)/normalizedOrbit R f K (m+1) := by linarith
  have hm := (le_div_iff₀ hm1).mp ht
  have he : (normalizedOrbit R f K (m+1)/normalizedOrbit R f K m-
      (‖P (orbit R f (m+1))‖^2/K^(m+2))/normalizedOrbit R f K (m+1))*
      normalizedOrbit R f K (m+1)=
      (normalizedOrbit R f K (m+1))^2/normalizedOrbit R f K m-
      ‖P (orbit R f (m+1))‖^2/K^(m+2) := by field_simp
  rwa [he] at hm

end KLSBelow25.ProjectionOrbitSlack
#print axioms KLSBelow25.ProjectionOrbitSlack.normalized_projection_energy_recurrence

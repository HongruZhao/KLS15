import JointObservationOperatorEndgame
noncomputable section
open InnerProductSpace ContinuousLinearMap AdjointOrbitRecurrence
namespace KLSBelow25.ProjectionOrbitSlack
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
set_option maxHeartbeats 1500000

def normalizedOrbit (R : H→L[ℝ]H) (f : H) (K : ℝ) (m : ℕ) : ℝ :=
  energy R f m / K^m

def shiftedOrbitRatio (R : H→L[ℝ]H) (f : H) (K : ℝ) (m : ℕ) : ℝ :=
  energy R f (m+1)/(K*energy R f m)

def shiftedObservation (R P : H→L[ℝ]H) (f : H) (K : ℝ) (m : ℕ) : ℝ :=
  ‖P (orbit R f (m+1))‖^2/(K*energy R f (m+1))

def shiftedSlack (R P : H→L[ℝ]H) (f : H) (K : ℝ) (m : ℕ) : ℝ :=
  (energy R f (m+2)+‖P (orbit R f (m+1))‖^2-
    energy R f (m+1)^2/energy R f m)/(K*energy R f (m+1))

theorem energy_zero_orbit (R : H→L[ℝ]H) (f : H) (m : ℕ)
    (h : energy R f m=0) : orbit R f m=0 := by
  have hh : ‖orbit R f m‖=0 := by
    have he : ‖orbit R f m‖^2=0 := h
    nlinarith [norm_nonneg (orbit R f m)]
  exact norm_eq_zero.mp hh

theorem energy_zero_succ (R : H→L[ℝ]H) (f : H) (m : ℕ)
    (h : energy R f m=0) : energy R f (m+1)=0 := by
  simp only [energy, orbit_succ, energy_zero_orbit R f m h, map_zero, norm_zero,
    zero_pow (by decide : (2:ℕ)≠0)]

theorem shifted_ratio_recurrence (R P : H→L[ℝ]H) (f : H) {K : ℝ}
    (hK : 0<K) (m : ℕ) :
    shiftedOrbitRatio R f K (m+1)=shiftedOrbitRatio R f K m-
      shiftedObservation R P f K m+shiftedSlack R P f K m := by
  by_cases h0 : energy R f m=0
  · have h1 := energy_zero_succ R f m h0
    have h2 := energy_zero_succ R f (m+1) h1
    simp [shiftedOrbitRatio,shiftedObservation,shiftedSlack,h0,h1,
      show m+1+1=m+2 by omega,h2]
  · by_cases h1 : energy R f (m+1)=0
    · have h2 := energy_zero_succ R f (m+1) h1
      simp [shiftedOrbitRatio,shiftedObservation,shiftedSlack,h1,
        show m+1+1=m+2 by omega,h2]
    · dsimp [shiftedOrbitRatio,shiftedObservation,shiftedSlack]
      rw [show m+1+1=m+2 by omega]
      field_simp
      ring

theorem shifted_slack_nonneg (R P : H→L[ℝ]H) (f : H) {K : ℝ}
    (hK : 0<K)
    (hcomp : ∀ v, ‖R v‖^2≤‖R.adjoint v‖^2+‖P v‖^2) (m : ℕ) :
    0 ≤ shiftedSlack R P f K m := by
  apply div_nonneg _ (mul_nonneg hK.le (by dsimp [energy]; positivity))
  by_cases h0 : energy R f m=0
  · have h1 := energy_zero_succ R f m h0
    have h2 := energy_zero_succ R f (m+1) h1
    rw [show m+1+1=m+2 by omega] at h2
    simp [h0,h1,h2]
  · have hp : 0<energy R f m := lt_of_le_of_ne (by dsimp [energy]; positivity) (Ne.symm h0)
    have hc := energy_cauchy R f m
    have hh := hcomp (orbit R f (m+1))
    have he : ‖R.adjoint (orbit R f (m+1))‖^2=energy R f (m+2) := by
      simp only [energy,show m+2=(m+1)+1 by omega,orbit_succ]
    rw [he] at hh
    have hb := hc.trans (mul_le_mul_of_nonneg_left hh hp.le)
    have hd : energy R f (m+1)^2/energy R f m ≤
        energy R f (m+2)+‖P (orbit R f (m+1))‖^2 :=
      (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using hb)
    linarith

theorem normalized_orbit_ratio_step (R : H→L[ℝ]H) (f : H) {K : ℝ}
    (hK : 0<K) (m : ℕ) :
    normalizedOrbit R f K (m+2)=shiftedOrbitRatio R f K (m+1)*normalizedOrbit R f K (m+1) := by
  by_cases h1 : energy R f (m+1)=0
  · have h2 := energy_zero_succ R f (m+1) h1
    simp [normalizedOrbit,shiftedOrbitRatio,h1,show m+1+1=m+2 by omega] at h2 ⊢
    simp [h2]
  · dsimp [normalizedOrbit,shiftedOrbitRatio]
    rw [show m+2=(m+1)+1 by omega,pow_succ]
    field_simp

theorem shifted_observation_nonneg (R P : H→L[ℝ]H) (f : H) {K : ℝ}
    (hK : 0<K) (m : ℕ) : 0 ≤ shiftedObservation R P f K m := by
  dsimp [shiftedObservation,energy]
  positivity

theorem shifted_ratio_eq_normalized (R : H→L[ℝ]H) (f : H) {K : ℝ}
    (hK : 0<K) (m : ℕ) :
    shiftedOrbitRatio R f K m=normalizedOrbit R f K (m+1)/normalizedOrbit R f K m := by
  dsimp [shiftedOrbitRatio,normalizedOrbit]
  rw [pow_succ]
  field_simp

theorem shifted_observation_eq_normalized (R P : H→L[ℝ]H) (f : H) {K : ℝ}
    (hK : 0<K) (m : ℕ) :
    shiftedObservation R P f K m=
      (‖P (orbit R f (m+1))‖^2/K^(m+2))/normalizedOrbit R f K (m+1) := by
  dsimp [shiftedObservation,normalizedOrbit]
  rw [show m+2=(m+1)+1 by omega,pow_succ]
  field_simp
  rw [pow_succ]
  ring

end KLSBelow25.ProjectionOrbitSlack
#print axioms KLSBelow25.ProjectionOrbitSlack.energy_zero_orbit
#print axioms KLSBelow25.ProjectionOrbitSlack.energy_zero_succ
#print axioms KLSBelow25.ProjectionOrbitSlack.shifted_ratio_recurrence
#print axioms KLSBelow25.ProjectionOrbitSlack.shifted_slack_nonneg
#print axioms KLSBelow25.ProjectionOrbitSlack.normalized_orbit_ratio_step

#print axioms KLSBelow25.ProjectionOrbitSlack.shifted_observation_nonneg
#print axioms KLSBelow25.ProjectionOrbitSlack.shifted_ratio_eq_normalized
#print axioms KLSBelow25.ProjectionOrbitSlack.shifted_observation_eq_normalized

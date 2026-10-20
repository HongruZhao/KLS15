import Mathlib

/-! The genuine bounded-Hilbert-operator adjoint-orbit recurrence of
manuscript Lemma 7.1.  The linear quadratic-form comparison is explicit;
it must ultimately come from the compatible tensor Hodge comparison. -/
noncomputable section
open InnerProductSpace
namespace AdjointOrbitRecurrence
variable {𝕜 H E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

theorem adjoint_pow (R : H →L[𝕜] H) (m : ℕ) :
    ContinuousLinearMap.adjoint (R ^ m) = (ContinuousLinearMap.adjoint R) ^ m := by
  simpa only [← ContinuousLinearMap.star_eq_adjoint] using star_pow R m

theorem observation_adjoint_norm (R : H →L[𝕜] H) (L : E →L[𝕜] H) (m : ℕ) :
    ‖(ContinuousLinearMap.adjoint L).comp ((ContinuousLinearMap.adjoint R) ^ m)‖ =
      ‖(R ^ m).comp L‖ := by
  rw [← adjoint_pow, ← ContinuousLinearMap.adjoint_comp]
  exact ContinuousLinearMap.adjoint.norm_map _

def orbit (R : H →L[𝕜] H) (f : H) (m : ℕ) : H :=
  ((ContinuousLinearMap.adjoint R) ^ m) f
def energy (R : H →L[𝕜] H) (f : H) (m : ℕ) : ℝ := ‖orbit R f m‖ ^ 2

@[simp] theorem orbit_zero (R : H →L[𝕜] H) (f : H) : orbit R f 0 = f := by
  simp [orbit]
@[simp] theorem orbit_succ (R : H →L[𝕜] H) (f : H) (m : ℕ) :
    orbit R f (m + 1) = ContinuousLinearMap.adjoint R (orbit R f m) := by
  simp only [orbit, pow_succ', ContinuousLinearMap.mul_apply]

theorem energy_nonneg (R : H →L[𝕜] H) (f : H) (m : ℕ) : 0 ≤ energy R f m :=
  sq_nonneg _

theorem energy_cauchy (R : H →L[𝕜] H) (f : H) (m : ℕ) :
    energy R f (m + 1) ^ 2 ≤ energy R f m * ‖R (orbit R f (m + 1))‖ ^ 2 := by
  have hi : ‖inner 𝕜 (orbit R f m) (R (orbit R f (m + 1)))‖ =
      energy R f (m + 1) := by
    rw [← ContinuousLinearMap.adjoint_inner_left, ← orbit_succ]
    simp [inner_self_eq_norm_sq_to_K, energy]
  have hc := norm_inner_le_norm (𝕜 := 𝕜) (orbit R f m) (R (orbit R f (m + 1)))
  rw [hi] at hc
  have he : 0 ≤ energy R f (m + 1) := energy_nonneg R f _
  have hs := (sq_le_sq₀ he (by positivity)).mpr hc
  simpa only [energy, mul_pow] using hs

theorem observation_orbit_sq_le (R : H →L[𝕜] H) (L : E →L[𝕜] H)
    (f : H) (m : ℕ) :
    ‖ContinuousLinearMap.adjoint L (orbit R f m)‖ ^ 2 ≤
      ‖(R ^ m).comp L‖ ^ 2 * ‖f‖ ^ 2 := by
  have hn := ((ContinuousLinearMap.adjoint L).comp
    ((ContinuousLinearMap.adjoint R) ^ m)).le_opNorm f
  rw [observation_adjoint_norm] at hn
  change ‖ContinuousLinearMap.adjoint L (orbit R f m)‖ ≤ _ at hn
  calc
    _ ≤ (‖(R ^ m).comp L‖ * ‖f‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
    _ = _ := by ring

theorem energy_recurrence (R : H →L[𝕜] H) (L : E →L[𝕜] H)
    (hcomparison : ∀ v : H, ‖R v‖ ^ 2 ≤
      ‖ContinuousLinearMap.adjoint R v‖ ^ 2 + ‖ContinuousLinearMap.adjoint L v‖ ^ 2)
    (f : H) (m : ℕ) (hm : 0 < energy R f m) :
    energy R f (m + 1) ^ 2 / energy R f m - ‖(R ^ (m + 1)).comp L‖ ^ 2 * ‖f‖ ^ 2 ≤
      energy R f (m + 2) := by
  have hc := energy_cauchy R f m
  have hcomp := hcomparison (orbit R f (m + 1))
  have hobs := observation_orbit_sq_le R L f (m + 1)
  have he : ‖ContinuousLinearMap.adjoint R (orbit R f (m + 1))‖ ^ 2 =
      energy R f (m + 2) := by
    simp only [energy, show m + 2 = (m + 1) + 1 by omega, orbit_succ]
  rw [he] at hcomp
  have hs : ‖R (orbit R f (m + 1))‖ ^ 2 ≤
      energy R f (m + 2) + ‖(R ^ (m + 1)).comp L‖ ^ 2 * ‖f‖ ^ 2 := by
    linarith
  have hh := hc.trans (mul_le_mul_of_nonneg_left hs hm.le)
  have hd : energy R f (m + 1) ^ 2 / energy R f m ≤
      energy R f (m + 2) + ‖(R ^ (m + 1)).comp L‖ ^ 2 * ‖f‖ ^ 2 :=
    (div_le_iff₀ hm).mpr (by simpa only [mul_comm] using hh)
  linarith

theorem energy_recurrence_unit (R : H →L[𝕜] H) (L : E →L[𝕜] H)
    (hcomparison : ∀ v : H, ‖R v‖ ^ 2 ≤
      ‖ContinuousLinearMap.adjoint R v‖ ^ 2 + ‖ContinuousLinearMap.adjoint L v‖ ^ 2)
    {f : H} (hf : ‖f‖ = 1) (m : ℕ) (hm : 0 < energy R f m) :
    energy R f (m + 1) ^ 2 / energy R f m - ‖(R ^ (m + 1)).comp L‖ ^ 2 ≤
      energy R f (m + 2) := by
  simpa only [hf, one_pow, mul_one] using energy_recurrence R L hcomparison f m hm

#print axioms observation_adjoint_norm
#print axioms energy_cauchy
#print axioms energy_recurrence
end AdjointOrbitRecurrence

import KLSConstantImprovement.ActualCanonicalMetricEnergyGraph
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Constructed canonical inverse and shifted resolvent

Lax--Milgram is applied to the actual inverse-Hessian graph and the
Brascamp--Lieb coercivity already proved there.  This constructs a single
canonical solution for each actual L2 datum.  No Poisson solution, Riesz
field, spectral operator or assumed response identity appears as an input.
-/

open MeasureTheory InnerProductSpace
open scoped BigOperators ContDiff RealInnerProductSpace

noncomputable section
namespace KLSConstantImprovement.ActualCanonicalMetricResolvent

open KLS KLSConstantImprovement.ActualCanonicalMetricEnergyGraph
variable {n : ℕ}

def canonicalInverseH1 {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 4 φ) (hpos : ∀ x, (coordinateHessian φ x).PosDef) :
    Lp ℝ 2 (potentialMeasure φ) →L[ℝ] CanonicalMetricH1 φ :=
  (canonicalMetricEnergy_isCoercive hφ hpos).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (canonicalMetricValue φ).adjoint

def canonicalInverse {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 4 φ) (hpos : ∀ x, (coordinateHessian φ x).PosDef) :
    Lp ℝ 2 (potentialMeasure φ) →L[ℝ] Lp ℝ 2 (potentialMeasure φ) :=
  (canonicalMetricValue φ).comp (canonicalInverseH1 hφ hpos)

theorem canonicalInverse_variational {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 4 φ) (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (g : Lp ℝ 2 (potentialMeasure φ)) (V : CanonicalMetricH1 φ) :
    canonicalMetricEnergy φ (canonicalInverseH1 hφ hpos g) V =
      inner ℝ g (canonicalMetricValue φ V) := by
  let hc := canonicalMetricEnergy_isCoercive hφ hpos
  rw [← hc.continuousLinearEquivOfBilin_apply]
  change inner ℝ (hc.continuousLinearEquivOfBilin
    (hc.continuousLinearEquivOfBilin.symm ((canonicalMetricValue φ).adjoint g))) V = _
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.adjoint_inner_left]

theorem canonicalInverse_unique {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 4 φ) (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (g : Lp ℝ 2 (potentialMeasure φ)) {U : CanonicalMetricH1 φ}
    (hU : ∀ V, canonicalMetricEnergy φ U V = inner ℝ g (canonicalMetricValue φ V)) :
    U = canonicalInverseH1 hφ hpos g := by
  let hc := canonicalMetricEnergy_isCoercive hφ hpos
  have he : (canonicalMetricValue φ).adjoint g = hc.continuousLinearEquivOfBilin U := by
    apply hc.unique_continuousLinearEquivOfBilin
    intro V
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact (hU V).symm
  calc
    U = hc.continuousLinearEquivOfBilin.symm (hc.continuousLinearEquivOfBilin U) :=
      (hc.continuousLinearEquivOfBilin.symm_apply_apply U).symm
    _ = hc.continuousLinearEquivOfBilin.symm ((canonicalMetricValue φ).adjoint g) := by rw [he]
    _ = canonicalInverseH1 hφ hpos g := rfl

theorem existsUnique_canonicalInverse {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 4 φ) (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (g : Lp ℝ 2 (potentialMeasure φ)) :
    ∃! U : CanonicalMetricH1 φ, ∀ V,
      canonicalMetricEnergy φ U V = inner ℝ g (canonicalMetricValue φ V) :=
  ⟨canonicalInverseH1 hφ hpos g, canonicalInverse_variational hφ hpos g,
    fun _ hU => canonicalInverse_unique hφ hpos g hU⟩

theorem canonicalInverse_energy_identity {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 4 φ) (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (g : Lp ℝ 2 (potentialMeasure φ)) :
    (∑ i, ‖canonicalMetricGradient φ i (canonicalInverseH1 hφ hpos g)‖ ^ 2) =
      inner ℝ g (canonicalInverse hφ hpos g) := by
  rw [← canonicalMetricEnergy_self]
  exact canonicalInverse_variational hφ hpos g _

theorem canonicalInverse_norm_le {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 4 φ) (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (g : Lp ℝ 2 (potentialMeasure φ)) :
    ‖canonicalInverse hφ hpos g‖ ≤ ‖g‖ := by
  let U := canonicalInverseH1 hφ hpos g
  have hP := canonicalMetricValue_norm_sq_le_energy hφ hpos U
  have hE := canonicalInverse_energy_identity hφ hpos g
  change (∑ i, ‖canonicalMetricGradient φ i U‖ ^ 2) = inner ℝ g (canonicalMetricValue φ U) at hE
  rw [hE] at hP
  have hi := real_inner_le_norm g (canonicalMetricValue φ U)
  change ‖canonicalMetricValue φ U‖ ≤ ‖g‖
  by_cases hz : ‖canonicalMetricValue φ U‖ = 0
  · rw [hz]
    exact norm_nonneg _
  · have hp := lt_of_le_of_ne (norm_nonneg (canonicalMetricValue φ U)) (Ne.symm hz)
    nlinarith

theorem canonicalInverse_symmetric {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 4 φ) (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (f g : Lp ℝ 2 (potentialMeasure φ)) :
    inner ℝ (canonicalInverse hφ hpos f) g = inner ℝ f (canonicalInverse hφ hpos g) := by
  have hf := canonicalInverse_variational hφ hpos f (canonicalInverseH1 hφ hpos g)
  have hg := canonicalInverse_variational hφ hpos g (canonicalInverseH1 hφ hpos f)
  rw [canonicalMetricEnergy_symm] at hg
  rw [real_inner_comm g (canonicalInverse hφ hpos f)]
  exact hg.symm.trans hf

theorem canonicalInverse_integral_eq_zero {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 4 φ) (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (g : Lp ℝ 2 (potentialMeasure φ)) :
    (∫ x, canonicalInverse hφ hpos g x ∂potentialMeasure φ) = 0 :=
  canonicalMetricValue_integral_eq_zero hφ.continuous _

def canonicalShiftedEnergy (φ : Space n → ℝ) (t : ℝ) :
    CanonicalMetricH1 φ →L[ℝ] CanonicalMetricH1 φ →L[ℝ] ℝ :=
  ((innerSL ℝ).bilinearComp (canonicalMetricValue φ) (canonicalMetricValue φ) :
    CanonicalMetricH1 φ →L[ℝ] CanonicalMetricH1 φ →L[ℝ] ℝ) +
    t • canonicalMetricEnergy φ

@[simp] theorem canonicalShiftedEnergy_apply (φ : Space n → ℝ) (t : ℝ)
    (U V : CanonicalMetricH1 φ) :
    canonicalShiftedEnergy φ t U V =
      inner ℝ (canonicalMetricValue φ U) (canonicalMetricValue φ V) +
        t * canonicalMetricEnergy φ U V := by
  simp [canonicalShiftedEnergy]

theorem canonicalShiftedEnergy_isCoercive (φ : Space n → ℝ) {t : ℝ} (ht : 0 < t) :
    IsCoercive (canonicalShiftedEnergy φ t) := by
  refine ⟨min 1 t, lt_min zero_lt_one ht, fun U => ?_⟩
  have hv := sq_nonneg ‖canonicalMetricValue φ U‖
  have he : 0 ≤ ∑ i : Fin n, ‖canonicalMetricGradient φ i U‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [canonicalShiftedEnergy_apply, real_inner_self_eq_norm_sq, canonicalMetricEnergy_self]
  have hn := canonicalMetricH1_norm_sq φ U
  have hvb := mul_le_mul_of_nonneg_right (min_le_left (1 : ℝ) t) hv
  have heb := mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) t) he
  calc
    min 1 t * ‖U‖ * ‖U‖ = min 1 t * ‖U‖ ^ 2 := by ring
    _ = min 1 t * ‖canonicalMetricValue φ U‖ ^ 2 +
        min 1 t * ∑ i : Fin n, ‖canonicalMetricGradient φ i U‖ ^ 2 := by rw [hn, mul_add]
    _ ≤ _ := add_le_add (by simpa using hvb) heb

def canonicalResolventH1 (φ : Space n → ℝ) {t : ℝ} (ht : 0 < t) :
    Lp ℝ 2 (potentialMeasure φ) →L[ℝ] CanonicalMetricH1 φ :=
  (canonicalShiftedEnergy_isCoercive φ ht).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (canonicalMetricValue φ).adjoint

def canonicalResolvent (φ : Space n → ℝ) {t : ℝ} (ht : 0 < t) :
    Lp ℝ 2 (potentialMeasure φ) →L[ℝ] Lp ℝ 2 (potentialMeasure φ) :=
  (canonicalMetricValue φ).comp (canonicalResolventH1 φ ht)

theorem canonicalResolvent_variational (φ : Space n → ℝ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) (V : CanonicalMetricH1 φ) :
    inner ℝ (canonicalResolvent φ ht g) (canonicalMetricValue φ V) +
      t * canonicalMetricEnergy φ (canonicalResolventH1 φ ht g) V =
        inner ℝ g (canonicalMetricValue φ V) := by
  let hc := canonicalShiftedEnergy_isCoercive φ ht
  change inner ℝ (canonicalMetricValue φ (canonicalResolventH1 φ ht g)) (canonicalMetricValue φ V) +
    t * canonicalMetricEnergy φ (canonicalResolventH1 φ ht g) V = _
  rw [← canonicalShiftedEnergy_apply, ← hc.continuousLinearEquivOfBilin_apply]
  change inner ℝ (hc.continuousLinearEquivOfBilin
    (hc.continuousLinearEquivOfBilin.symm ((canonicalMetricValue φ).adjoint g))) V = _
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.adjoint_inner_left]

theorem canonicalResolvent_energy_identity (φ : Space n → ℝ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) :
    ‖canonicalResolvent φ ht g‖ ^ 2 +
      t * canonicalMetricEnergy φ (canonicalResolventH1 φ ht g) (canonicalResolventH1 φ ht g) =
        inner ℝ g (canonicalResolvent φ ht g) := by
  simpa only [canonicalResolvent, ContinuousLinearMap.comp_apply, real_inner_self_eq_norm_sq] using
    canonicalResolvent_variational φ ht g (canonicalResolventH1 φ ht g)

theorem canonicalResolvent_symmetric (φ : Space n → ℝ) {t : ℝ} (ht : 0 < t)
    (f g : Lp ℝ 2 (potentialMeasure φ)) :
    inner ℝ (canonicalResolvent φ ht f) g = inner ℝ f (canonicalResolvent φ ht g) := by
  have hf := canonicalResolvent_variational φ ht f (canonicalResolventH1 φ ht g)
  have hg := canonicalResolvent_variational φ ht g (canonicalResolventH1 φ ht f)
  change inner ℝ (canonicalResolvent φ ht f) (canonicalResolvent φ ht g) + _ =
    inner ℝ f (canonicalResolvent φ ht g) at hf
  change inner ℝ (canonicalResolvent φ ht g) (canonicalResolvent φ ht f) + _ =
    inner ℝ g (canonicalResolvent φ ht f) at hg
  rw [real_inner_comm (canonicalResolvent φ ht f) (canonicalResolvent φ ht g),
    canonicalMetricEnergy_symm φ (canonicalResolventH1 φ ht g),
    real_inner_comm (canonicalResolvent φ ht f) g] at hg
  exact hg.symm.trans hf

theorem canonicalResolvent_norm_le (φ : Space n → ℝ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) :
    ‖canonicalResolvent φ ht g‖ ≤ ‖g‖ := by
  have he := canonicalResolvent_energy_identity φ ht g
  have hp : 0 ≤ canonicalMetricEnergy φ (canonicalResolventH1 φ ht g)
      (canonicalResolventH1 φ ht g) := by
    rw [canonicalMetricEnergy_self]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hi := real_inner_le_norm g (canonicalResolvent φ ht g)
  by_cases hz : ‖canonicalResolvent φ ht g‖ = 0
  · rw [hz]
    exact norm_nonneg _
  · have hn := lt_of_le_of_ne (norm_nonneg (canonicalResolvent φ ht g)) (Ne.symm hz)
    nlinarith [mul_nonneg ht.le hp]

end KLSConstantImprovement.ActualCanonicalMetricResolvent
end

#print axioms KLSConstantImprovement.ActualCanonicalMetricResolvent.existsUnique_canonicalInverse
#print axioms KLSConstantImprovement.ActualCanonicalMetricResolvent.canonicalInverse_norm_le
#print axioms KLSConstantImprovement.ActualCanonicalMetricResolvent.canonicalInverse_symmetric
#print axioms KLSConstantImprovement.ActualCanonicalMetricResolvent.canonicalResolvent_variational
#print axioms KLSConstantImprovement.ActualCanonicalMetricResolvent.canonicalResolvent_symmetric
#print axioms KLSConstantImprovement.ActualCanonicalMetricResolvent.canonicalResolvent_norm_le

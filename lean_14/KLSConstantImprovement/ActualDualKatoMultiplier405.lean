import KLSConstantImprovement.ActualDualBumpControl405
import KLSConstantImprovement.ActualSmoothKatoRegularizer405
import KLSConstantImprovement.ActualNaturalMassWeakDerivative405

/-! Concrete smooth nonlinear multipliers of the actual bilinear pair
(u,p). Values and differentials are literal; actual compact weak test
admissibility follows from the already constructed dual chain. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualDualKatoMultiplier405
open KLS ActualBoundedCanonicalSource ActualNaturalDualJoint405 ActualDualBumpControl405
open ActualSmoothKatoRegularizer405 ActualNaturalMassWeakDerivative405
open ActualSourceNaturalGaffney405 ActualSourceNaturalTargetCurvatureDomain405
open ActualSourceNaturalHessian405 ActualSourceLocalizedGaffney405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

def dualScalarMultiplier (F : ℝ → ℝ) (k : ℕ) (v : DualIndex n → ℝ) : ℝ :=
  dualBump k v * F (dualMass v)

theorem dualMass_contDiff : ContDiff ℝ 1 (dualMass (n := n)) := by
  unfold dualMass
  fun_prop

theorem katoFirst_contDiff {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 1 (katoFirst ε) := by
  have hr : ContDiff ℝ 1 (katoRho ε) :=
    ((contDiff_id.pow 2).add contDiff_const).sqrt (fun t => by nlinarith [sq_nonneg t])
  have hs : ContDiff ℝ 1 (katoRegularizer ε) := (katoRegularizer_contDiff hε).of_le (by norm_num)
  exact contDiff_id.div ((contDiff_const.mul hr).mul hs) (fun t => by
    have hp := katoRho_positive hε t
    have hq := katoRegularizer_positive hε t
    positivity)

theorem dualScalarMultiplier_contDiff_compact {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (k : ℕ) :
    ContDiff ℝ 1 (dualScalarMultiplier (n := n) F k) ∧ HasCompactSupport (dualScalarMultiplier (n := n) F k) :=
  ⟨(dualBump_contDiff k).mul (hF.comp dualMass_contDiff), (dualBump_compact k).mul_right⟩

theorem dualScalarMultiplier_differential {F F' : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) (hderiv : ∀ t, HasDerivAt F (F' t) t)
    (k : ℕ) (v z : DualIndex n → ℝ) :
    fderiv ℝ (dualScalarMultiplier F k) v z =
      dualBump k v * F' (dualMass v) * fderiv ℝ dualMass v z +
        F (dualMass v) * fderiv ℝ (dualBump k) v z := by
  have hcurve : HasDerivAt (fun t : ℝ => v + t • z) z 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const z).const_add v
  have hm : HasDerivAt (fun t : ℝ => dualMass (v + t • z)) (fderiv ℝ dualMass v z) 0 := by
    simpa only [Function.comp_def] using
      (dualMass_contDiff.differentiable one_ne_zero v).hasFDerivAt.comp_hasDerivAt_of_eq 0 hcurve (by simp)
  have hf : HasDerivAt (fun t : ℝ => F (dualMass (v + t • z)))
      (F' (dualMass v) * fderiv ℝ dualMass v z) 0 := by
    simpa only [Function.comp_def, zero_smul, add_zero] using (hderiv (dualMass v)).comp_of_eq 0 hm (by simp)
  have hb : HasDerivAt (fun t : ℝ => dualBump k (v + t • z)) (fderiv ℝ (dualBump k) v z) 0 := by
    simpa only [Function.comp_def] using
      ((dualBump_contDiff k).differentiable one_ne_zero v).hasFDerivAt.comp_hasDerivAt_of_eq 0 hcurve (by simp)
  have hp := hb.mul hf
  have hp' : HasDerivAt (fun t : ℝ => dualScalarMultiplier F k (v + t • z))
      (fderiv ℝ (dualBump k) v z * F (dualMass v) +
        dualBump k v * (F' (dualMass v) * fderiv ℝ dualMass v z)) 0 := by
    convert hp using 1 <;> (try funext t) <;> simp only [dualScalarMultiplier, Pi.mul_apply, zero_smul, add_zero]
  have hc : HasDerivAt (fun t : ℝ => dualScalarMultiplier F k (v + t • z))
      (fderiv ℝ (dualScalarMultiplier F k) v z) 0 := by
    simpa only [Function.comp_def] using
      ((dualScalarMultiplier_contDiff_compact hF k).1.differentiable one_ne_zero v).hasFDerivAt.comp_hasDerivAt_of_eq
        0 hcurve (by simp)
  have he := hc.unique hp'
  rw [he]
  ring

theorem actual_dualMass_eq_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    (fun x => dualMass (fun a => dualValue d g a x)) =ᵐ[potentialMeasure d.potential]
      sourceVectorMass d.potential (naturalCanonicalFlux d g) := by
  filter_upwards [hessian_mul_naturalCanonicalFlux_ae d g] with x hx
  have hp (i : Fin n) : naturalCanonicalRawGradient d g i x =
      (coordinateHessian d.potential x *ᵥ (fun j => naturalCanonicalFlux d g j x)) i := (congrFun hx i).symm
  simp only [dualMass, dualValue, Sum.elim_inl, Sum.elim_inr]
  simp_rw [hp]
  simp only [sourceVectorMass, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem actual_dualMass_derivative (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) (b : Fin n) (x : Space n) :
    fderiv ℝ dualMass (fun a => dualValue d g a x) (fun a => dualDerivative d g Du a b x) =
      naturalMassRawDerivative d g Du b x := by
  simp only [dualMass_differential, dualValue, dualDerivative, Sum.elim_inl, Sum.elim_inr,
    naturalMassRawDerivative]

theorem actual_dual_scalar_multiplier_derivative_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) {F F' : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) (hderiv : ∀ t, HasDerivAt F (F' t) t) (k : ℕ) (b : Fin n) :
    dualSourceDerivative d g Du (dualScalarMultiplier F k) b =ᵐ[potentialMeasure d.potential]
      fun x => dualSource d g (dualBump k) x * F' (sourceVectorMass d.potential (naturalCanonicalFlux d g) x) *
        naturalMassRawDerivative d g Du b x +
          F (sourceVectorMass d.potential (naturalCanonicalFlux d g) x) * dualSourceDerivative d g Du (dualBump k) b x := by
  filter_upwards [actual_dualMass_eq_ae d g] with x hx
  unfold dualSourceDerivative
  rw [dualScalarMultiplier_differential hF hderiv, actual_dualMass_derivative, hx]
  rfl

end KLSConstantImprovement.ActualDualKatoMultiplier405
#print axioms KLSConstantImprovement.ActualDualKatoMultiplier405.katoFirst_contDiff
#print axioms KLSConstantImprovement.ActualDualKatoMultiplier405.dualScalarMultiplier_contDiff_compact
#print axioms KLSConstantImprovement.ActualDualKatoMultiplier405.dualScalarMultiplier_differential
#print axioms KLSConstantImprovement.ActualDualKatoMultiplier405.actual_dualMass_eq_ae
#print axioms KLSConstantImprovement.ActualDualKatoMultiplier405.actual_dualMass_derivative
#print axioms KLSConstantImprovement.ActualDualKatoMultiplier405.actual_dual_scalar_multiplier_derivative_ae

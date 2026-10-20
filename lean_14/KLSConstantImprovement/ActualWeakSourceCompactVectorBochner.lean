import KLSConstantImprovement.ActualSourceVectorBochnerFirstOrderDomain
import KLS.WeakBochner
import KLS.WeakMomentLocalEssentialBounds

/-!
The source-vector Bochner identity for an actual C1,1 source potential.
Only the vector coordinates are smooth. The potential Hessian is its actual
almost-everywhere derivative, and the source adjoint is differentiated weakly.
This removes the earlier classical C2 source hypothesis from the compact
identity. Passage to nonsmooth vector coordinates is a separate limit.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators ContDiff Topology NNReal ENNReal Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualWeakSourceCompactVectorBochner
open KLS ActualCompactSourceVectorBochner ActualSourceVectorBochnerFirstOrderDomain
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem locallyLipschitz_sourceAdjoint {φ b : Space n → ℝ}
    (hG : LocallyLipschitz (gradient φ)) (hb : ContDiff ℝ 2 b) (j : Fin n) :
    LocallyLipschitz (coordinateSourceAdjoint φ b j) := by
  have hmul : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.1 * p.2) :=
    contDiff_fst.mul contDiff_snd
  have hφj := locallyLipschitz_coordinateDerivative_of_gradient hG j
  exact (hmul.locallyLipschitz.comp
    (hφj.prodMk (hb.of_le (by norm_num)).locallyLipschitz)).sub
      (contDiff_coordinateDerivative hb (m := 1) (by norm_num) j).locallyLipschitz

theorem coordinateDerivative_sourceAdjoint_at {φ b : Space n → ℝ}
    (i j : Fin n) {x : Space n}
    (hφj : DifferentiableAt ℝ (coordinateDerivative φ j) x) (hb : ContDiff ℝ 2 b) :
    coordinateDerivative (coordinateSourceAdjoint φ b j) i x =
      coordinateHessian φ x i j * b x +
        coordinateDerivative φ j x * coordinateDerivative b i x -
        coordinateHessian b x i j := by
  have hbx := hb.differentiable (by norm_num) x
  have hbj := (contDiff_coordinateDerivative hb (m := 1) (by norm_num) j).differentiable
    (by norm_num) x
  unfold coordinateSourceAdjoint
  rw [coordinateDerivative_sub
    (f := fun y => coordinateDerivative φ j y * b y)
    (g := coordinateDerivative b j) (hφj.mul hbx) hbj,
    coordinateDerivative_mul (f := coordinateDerivative φ j) (g := b) hφj hbx]
  rfl

/-- The actual adjoint commutator is a genuine weak derivative, with all
its local integrability derived from C1,1 source regularity. -/
theorem weak_sourceAdjoint_derivative {φ b : Space n → ℝ}
    (hG : LocallyLipschitz (gradient φ)) (hb : ContDiff ℝ 2 b) (i j : Fin n) :
    HasLocalWeakCoordinateDerivative (coordinateSourceAdjoint φ b j)
      (fun x => coordinateHessian φ x i j * b x +
        coordinateDerivative φ j x * coordinateDerivative b i x -
        coordinateHessian b x i j) i ∧
    (∀ S : Set (Space n), IsCompact S → MemLp
      (fun x => coordinateHessian φ x i j * b x +
        coordinateDerivative φ j x * coordinateDerivative b i x -
        coordinateHessian b x i j) ∞ (volume.restrict S)) := by
  have he : coordinateDerivative (coordinateSourceAdjoint φ b j) i =ᵐ[volume]
      (fun x => coordinateHessian φ x i j * b x +
        coordinateDerivative φ j x * coordinateDerivative b i x -
        coordinateHessian b x i j) := by
    filter_upwards [locallyLipschitz_ae_differentiableAt (μ := volume)
      (locallyLipschitz_coordinateDerivative_of_gradient hG j)] with x hx
    exact coordinateDerivative_sourceAdjoint_at i j hx hb
  have hl := locallyLipschitz_sourceAdjoint hG hb j
  refine ⟨(hasLocalWeakCoordinateDerivative_of_locallyLipschitz hl i).congr_ae
    Filter.EventuallyEq.rfl he, ?_⟩
  intro S hS
  exact (memLp_congr_ae (ae_restrict_of_ae he)).mp
    (memLp_top_coordinateDerivative_of_locallyLipschitz hl i hS)

/-- A compact smooth left coordinate can pair with a genuine weak right
derivative at C1 source regularity. The right coordinate need not be C1. -/
theorem compact_source_adjoint_pair_weak {φ a g G : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a)
    {i : Fin n} (hGw : HasLocalWeakCoordinateDerivative g G i) :
    (∫ x, coordinateSourceAdjoint φ a i x * g x ∂potentialMeasure φ) =
      ∫ x, a x * G x ∂potentialMeasure φ := by
  have hw := hGw (fun x => Real.exp (-φ x) * a x)
    (hφ.neg.exp.mul ha) hc.mul_left
  have hl : (∫ x, g x * coordinateDerivative (fun y => Real.exp (-φ y) * a y) i x) =
      -(∫ x, coordinateSourceAdjoint φ a i x * g x ∂potentialMeasure φ) := by
    rw [← integral_neg, integral_potentialMeasure hφ.continuous.measurable]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      have hρ : DifferentiableAt ℝ (fun y => Real.exp (-φ y)) x :=
        ((hφ.differentiable (by norm_num) x).neg).exp
      rw [coordinateDerivative_mul hρ (ha.differentiable (by norm_num) x)]
      change g x * (fderiv ℝ (fun y => Real.exp (-φ y)) x
        (EuclideanSpace.single i 1) * a x +
          Real.exp (-φ x) * coordinateDerivative a i x) = _
      rw [fderiv_exp_neg_apply (hφ.differentiable (by norm_num) x)]
      dsimp only [coordinateSourceAdjoint, coordinateDerivative]
      ring
  have hr : (∫ x, G x * (Real.exp (-φ x) * a x)) =
      ∫ x, a x * G x ∂potentialMeasure φ := by
    rw [integral_potentialMeasure hφ.continuous.measurable]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  rw [hl, hr] at hw
  linarith

/-- The literal compact vector-coordinate identity at C1,1 source
regularity. No classical second derivative of the source is used. -/
theorem compact_left_source_vector_bochner_coordinate_C11 {φ a b : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hG : LocallyLipschitz (gradient φ))
    (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hca : HasCompactSupport a) (i j : Fin n) :
    (∫ x, coordinateSourceAdjoint φ a i x * coordinateSourceAdjoint φ b j x
      ∂potentialMeasure φ) =
      (∫ x, coordinateHessian φ x i j * a x * b x ∂potentialMeasure φ) +
        ∫ x, coordinateDerivative a j x * coordinateDerivative b i x
          ∂potentialMeasure φ := by
  have ha1 : ContDiff ℝ 1 a := ha.of_le (by norm_num)
  have hb1 : ContDiff ℝ 1 b := hb.of_le (by norm_num)
  have hbi : ContDiff ℝ 1 (coordinateDerivative b i) :=
    contDiff_coordinateDerivative hb (by norm_num) i
  have hfirst := compact_source_adjoint_pair_weak hφ ha1 hca
    (weak_sourceAdjoint_derivative hG hb i j).1
  have he : (fun x => a x * (coordinateHessian φ x i j * b x +
      coordinateDerivative φ j x * coordinateDerivative b i x - coordinateHessian b x i j)) =
      (fun x => coordinateHessian φ x i j * a x * b x +
        a x * coordinateSourceAdjoint φ (coordinateDerivative b i) j x) := by
    funext x
    have hs := (coordinateHessian_symmetric hb x).apply i j
    change coordinateHessian b x j i = coordinateHessian b x i j at hs
    dsimp only [coordinateSourceAdjoint]
    change _ = coordinateHessian φ x i j * a x * b x +
      a x * (coordinateDerivative φ j x * coordinateDerivative b i x - coordinateHessian b x j i)
    rw [hs]
    ring
  have hHloc : LocallyIntegrable (fun x => coordinateHessian φ x i j) volume :=
    locallyIntegrable_coordinateDerivative_of_locallyLipschitz
      (locallyLipschitz_coordinateDerivative_of_gradient hG j) i
  have hcurv : Integrable (fun x => coordinateHessian φ x i j * a x * b x)
      (potentialMeasure φ) := by
    have hm : Integrable (fun x => coordinateHessian φ x i j * (a * b) x)
        (potentialMeasure φ) := integrable_raw_mul_compact_potential hφ.continuous hHloc
      (ha.continuous.mul hb.continuous) hca.mul_right
    simpa only [Pi.mul_apply, mul_assoc] using hm
  have hadj : Continuous (coordinateSourceAdjoint φ (coordinateDerivative b i) j) := by
    exact (((contDiff_coordinateDerivative hφ (m := 0) (by norm_num) j).continuous).mul
      hbi.continuous).sub
        (contDiff_coordinateDerivative hbi (m := 0) (by norm_num) j).continuous
  have hrem : Integrable
      (fun x => a x * coordinateSourceAdjoint φ (coordinateDerivative b i) j x)
      (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      (ha.continuous.mul hadj) hca.mul_right
  rw [he, integral_add hcurv hrem] at hfirst
  have hsecond := compact_source_adjoint_ibp hφ hbi ha1 hca j
  have hr : (∫ x, a x * coordinateSourceAdjoint φ (coordinateDerivative b i) j x
      ∂potentialMeasure φ) =
      ∫ x, coordinateDerivative a j x * coordinateDerivative b i x ∂potentialMeasure φ := by
    calc
      _ = ∫ x, coordinateSourceAdjoint φ (coordinateDerivative b i) j x * a x
          ∂potentialMeasure φ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      _ = ∫ x, coordinateDerivative b i x * coordinateDerivative a j x
          ∂potentialMeasure φ := hsecond
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
  rwa [hr] at hfirst

end KLSConstantImprovement.ActualWeakSourceCompactVectorBochner

#print axioms KLSConstantImprovement.ActualWeakSourceCompactVectorBochner.locallyLipschitz_sourceAdjoint
#print axioms KLSConstantImprovement.ActualWeakSourceCompactVectorBochner.coordinateDerivative_sourceAdjoint_at
#print axioms KLSConstantImprovement.ActualWeakSourceCompactVectorBochner.weak_sourceAdjoint_derivative
#print axioms KLSConstantImprovement.ActualWeakSourceCompactVectorBochner.compact_source_adjoint_pair_weak
#print axioms KLSConstantImprovement.ActualWeakSourceCompactVectorBochner.compact_left_source_vector_bochner_coordinate_C11

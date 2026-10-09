import PolynomialDerivativeGrowth

/-! Preservation of a genuine pointwise Hessian upper bound under the
actual affine and damping transformations used by the released approximation. -/

open MeasureTheory InnerProductSpace Set Filter Metric Matrix
open scoped ENNReal ContDiff Topology RealInnerProductSpace BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ}

def HasHessianUpperBound (V : Space n → ℝ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ x v : Space n,
    fderiv ℝ (fderiv ℝ V) x v v ≤ M * ‖v‖ ^ 2

lemma secondFrechet_add {V W : Space n → ℝ}
    (hV : ContDiff ℝ 2 V) (hW : ContDiff ℝ 2 W) (x v : Space n) :
    fderiv ℝ (fderiv ℝ (fun y => V y + W y)) x v v =
      fderiv ℝ (fderiv ℝ V) x v v + fderiv ℝ (fderiv ℝ W) x v v := by
  have hh := congrArg (fun T => T (fun _ : Fin 2 => v))
    (fun_iteratedFDeriv_add_apply hV.contDiffAt hW.contDiffAt (x := x))
  simpa only [iteratedFDeriv_two_apply, _root_.add_apply] using hh

lemma secondFrechet_const (c : ℝ) (x v : Space n) :
    fderiv ℝ (fderiv ℝ (fun _ : Space n => c)) x v v = 0 := by simp

lemma secondFrechet_const_mul {V : Space n → ℝ}
    (hV : ContDiff ℝ 2 V) (a : ℝ) (x v : Space n) :
    fderiv ℝ (fderiv ℝ (fun y => a * V y)) x v v =
      a * fderiv ℝ (fderiv ℝ V) x v v := by
  have hh := congrArg (fun T => T (fun _ : Fin 2 => v))
    (iteratedFDeriv_const_smul_apply' (a := a) hV.contDiffAt (x := x))
  simpa only [iteratedFDeriv_two_apply, smul_eq_mul,
    _root_.smul_apply] using hh

lemma secondFrechet_norm_sq (x v : Space n) :
    fderiv ℝ (fderiv ℝ (fun y : Space n => ‖y‖ ^ 2)) x v v = 2 * ‖v‖ ^ 2 := by
  let L : Space n →L[ℝ] Space n →L[ℝ] ℝ :=
    (2 : ℝ) • (innerSL ℝ : Space n →L[ℝ] Space n →L[ℝ] ℝ)
  have hd : fderiv ℝ (fun y : Space n => ‖y‖ ^ 2) = ⇑L := by
    funext y
    rw [fderiv_norm_sq_apply]
    ext z
    simp [L]
    exact (innerSL_apply_apply ℝ y z).symm
  have hLd : fderiv ℝ (⇑L) x = L := L.fderiv
  rw [hd, hLd]
  simp only [L, _root_.smul_apply, smul_eq_mul]
  rw [innerSL_apply_apply ℝ v v, real_inner_self_eq_norm_sq]

theorem HasHessianUpperBound.const (c : ℝ) :
    HasHessianUpperBound (fun _ : Space n => c) :=
  ⟨0, le_rfl, fun x v => by rw [secondFrechet_const, zero_mul]⟩

theorem HasHessianUpperBound.add {V W : Space n → ℝ}
    (hV : HasHessianUpperBound V) (hW : HasHessianUpperBound W)
    (hVs : ContDiff ℝ 2 V) (hWs : ContDiff ℝ 2 W) :
    HasHessianUpperBound (fun x => V x + W x) := by
  obtain ⟨M, hM, hb⟩ := hV
  obtain ⟨N, hN, hc⟩ := hW
  refine ⟨M + N, add_nonneg hM hN, fun x v => ?_⟩
  rw [secondFrechet_add hVs hWs]
  nlinarith [hb x v, hc x v]

theorem HasHessianUpperBound.sub_const {V : Space n → ℝ}
    (hV : HasHessianUpperBound V) (hVs : ContDiff ℝ 2 V) (c : ℝ) :
    HasHessianUpperBound (fun x => V x - c) := by
  simpa only [sub_eq_add_neg] using hV.add (HasHessianUpperBound.const (-c)) hVs contDiff_const

lemma secondFrechet_comp_clm_add {V : Space n → ℝ}
    (hVs : ContDiff ℝ 2 V) (L : Space n →L[ℝ] Space n) (b x v : Space n) :
    fderiv ℝ (fderiv ℝ (fun y => V (L y + b))) x v v =
      fderiv ℝ (fderiv ℝ V) (L x + b) (L v) (L v) := by
  have hs : ContDiff ℝ 2 (fun y => V (y + b)) := hVs.comp (contDiff_id.add contDiff_const)
  have he : iteratedFDeriv ℝ 2 (fun y => V (L y + b)) x =
      (iteratedFDeriv ℝ 2 V (L x + b)).compContinuousLinearMap (fun _ => L) := by
    rw [show (fun y => V (L y + b)) = (fun y => V (y + b)) ∘ L from rfl,
      L.iteratedFDeriv_comp_right hs x le_rfl, iteratedFDeriv_comp_add_right]
  have hh := congrArg (fun T => T (fun _ : Fin 2 => v)) he
  simpa only [iteratedFDeriv_two_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply] using hh

theorem HasHessianUpperBound.comp_clm_add {V : Space n → ℝ}
    (hV : HasHessianUpperBound V) (hVs : ContDiff ℝ 2 V)
    (L : Space n →L[ℝ] Space n) (b : Space n) :
    HasHessianUpperBound (fun x => V (L x + b)) := by
  obtain ⟨M, hM, hb⟩ := hV
  refine ⟨M * ‖L‖ ^ 2, by positivity, fun x v => ?_⟩
  rw [secondFrechet_comp_clm_add hVs]
  have hn : ‖L v‖ ^ 2 ≤ ‖L‖ ^ 2 * ‖v‖ ^ 2 := by
    nlinarith [L.le_opNorm v, norm_nonneg (L v), norm_nonneg L, norm_nonneg v]
  exact (hb _ _).trans (by nlinarith [mul_le_mul_of_nonneg_left hn hM])

theorem HasHessianUpperBound.comp_continuousAffineMap {V : Space n → ℝ}
    (hV : HasHessianUpperBound V) (hVs : ContDiff ℝ 2 V)
    (F : Space n →ᴬ[ℝ] Space n) :
    HasHessianUpperBound (fun x => V (F x)) := by
  have he : (fun x => V (F x)) = fun x => V (F.contLinear x + F 0) := by
    funext x
    congr 1
    simpa using F.map_vadd (0 : Space n) x
  rw [he]
  exact hV.comp_clm_add hVs F.contLinear (F 0)

theorem HasHessianUpperBound.dampedPotential {V : Space n → ℝ}
    (hV : HasHessianUpperBound V) (hVs : ContDiff ℝ 2 V)
    (μ : Measure (Space n)) {ε : ℝ} (hε : 0 ≤ ε) :
    HasHessianUpperBound (dampedPotential μ V ε) := by
  have hn : ContDiff ℝ 2 (fun z : Space n => ‖z‖ ^ 2) := contDiff_norm_sq ℝ
  have hεn : HasHessianUpperBound (fun z : Space n => ε * ‖z‖ ^ 2) := by
    refine ⟨2 * ε, by positivity, fun x v => ?_⟩
    rw [secondFrechet_const_mul hn, secondFrechet_norm_sq]
    ring_nf
    exact le_rfl
  exact (hV.add hεn hVs (contDiff_const.mul hn)).add
    (HasHessianUpperBound.const _)
    (hVs.add (contDiff_const.mul hn)) contDiff_const

theorem HasHessianUpperBound.affineTransformedPotential {V : Space n → ℝ}
    (hV : HasHessianUpperBound V) (hVs : ContDiff ℝ 2 V)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) (hA : A.det ≠ 0) :
    HasHessianUpperBound (affineTransformedPotential V A b hA) := by
  exact (hV.comp_continuousAffineMap hVs
    (affineMatrixEquiv A b hA).symm.toContinuousAffineMap).sub_const
      (hVs.comp (affineMatrixEquiv A b hA).symm.toContinuousAffineMap.contDiff) _

theorem hasHessianUpperBound_gaussianSmoothedPotential
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hc : IsCompact μ.support) {r : ℝ} (hr : r ≠ 0) :
    HasHessianUpperBound (gaussianSmoothedPotential μ r) :=
  ⟨(r⁻¹) ^ 2, sq_nonneg _, secondFrechet_gaussianSmoothedPotential_le hc hr⟩

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.HasHessianUpperBound.dampedPotential
#print axioms KLS.DeterministicBridgeIntegration.HasHessianUpperBound.affineTransformedPotential

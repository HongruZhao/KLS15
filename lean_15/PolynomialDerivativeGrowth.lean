import GaussianPotentialDerivativeBounds
import KLS.GlobalDampingDensity

/-! Polynomial growth of actual iterated derivatives, including order zero.
This is an analytic regularity property, with no spectral inequality inside
its definition. -/

open MeasureTheory InnerProductSpace Set Filter Metric Matrix
open scoped ENNReal ContDiff Topology RealInnerProductSpace BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ}

def HasPolynomialDerivativeGrowth (f : Space n → ℝ) : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ x,
    ‖iteratedFDeriv ℝ m f x‖ ≤ C * (1 + ‖x‖) ^ k

theorem HasPolynomialDerivativeGrowth.const (c : ℝ) :
    HasPolynomialDerivativeGrowth (fun _ : Space n => c) := by
  intro m
  refine ⟨‖c‖, norm_nonneg _, 0, ?_⟩
  intro x
  by_cases hm : m = 0
  · subst m
    simp
  · rw [iteratedFDeriv_const_of_ne hm]
    simp

theorem HasPolynomialDerivativeGrowth.const_mul
    {f : Space n → ℝ} (hf : HasPolynomialDerivativeGrowth f)
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (a : ℝ) :
    HasPolynomialDerivativeGrowth (fun x => a * f x) := by
  intro m
  obtain ⟨C, hC, k, hb⟩ := hf m
  refine ⟨‖a‖ * C, mul_nonneg (norm_nonneg _) hC, k, fun x => ?_⟩
  have he : (fun x => a * f x) = a • f := rfl
  rw [he, iteratedFDeriv_const_smul_apply (hs.contDiffAt.of_le (by simp)), norm_smul]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb x) (norm_nonneg a)

theorem HasPolynomialDerivativeGrowth.add
    {f g : Space n → ℝ} (hf : HasPolynomialDerivativeGrowth f)
    (hg : HasPolynomialDerivativeGrowth g)
    (hfs : ContDiff ℝ (⊤ : ℕ∞) f) (hgs : ContDiff ℝ (⊤ : ℕ∞) g) :
    HasPolynomialDerivativeGrowth (fun x => f x + g x) := by
  intro m
  obtain ⟨C, hC, k, hb⟩ := hf m
  obtain ⟨D, hD, l, hc⟩ := hg m
  refine ⟨C + D, add_nonneg hC hD, k + l, fun x => ?_⟩
  rw [fun_iteratedFDeriv_add_apply (hfs.contDiffAt.of_le (by simp))
    (hgs.contDiffAt.of_le (by simp))]
  have hk : (1 + ‖x‖) ^ k ≤ (1 + ‖x‖) ^ (k + l) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg x]) (by omega)
  have hl : (1 + ‖x‖) ^ l ≤ (1 + ‖x‖) ^ (k + l) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg x]) (by omega)
  calc
    _ ≤ ‖iteratedFDeriv ℝ m f x‖ + ‖iteratedFDeriv ℝ m g x‖ := norm_add_le _ _
    _ ≤ C * (1 + ‖x‖) ^ k + D * (1 + ‖x‖) ^ l := add_le_add (hb x) (hc x)
    _ ≤ C * (1 + ‖x‖) ^ (k + l) + D * (1 + ‖x‖) ^ (k + l) :=
      add_le_add (mul_le_mul_of_nonneg_left hk hC) (mul_le_mul_of_nonneg_left hl hD)
    _ = _ := by ring

theorem HasPolynomialDerivativeGrowth.sub
    {f g : Space n → ℝ} (hf : HasPolynomialDerivativeGrowth f)
    (hg : HasPolynomialDerivativeGrowth g)
    (hfs : ContDiff ℝ (⊤ : ℕ∞) f) (hgs : ContDiff ℝ (⊤ : ℕ∞) g) :
    HasPolynomialDerivativeGrowth (fun x => f x - g x) := by
  simpa only [neg_one_mul, sub_eq_add_neg] using
    hf.add (hg.const_mul hgs (-1)) hfs (contDiff_const.mul hgs)

/-- Actual affine changes of variables preserve polynomial growth of every
iterated derivative, including order zero. -/
theorem HasPolynomialDerivativeGrowth.comp_clm_add
    {f : Space n → ℝ} (hf : HasPolynomialDerivativeGrowth f)
    (hfs : ContDiff ℝ (⊤ : ℕ∞) f) (L : Space n →L[ℝ] Space n) (b : Space n) :
    HasPolynomialDerivativeGrowth (fun x => f (L x + b)) := by
  intro m
  obtain ⟨C, hC, k, hb⟩ := hf m
  let D : ℝ := 1 + ‖L‖ + ‖b‖
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨C * D ^ k * ‖L‖ ^ m, by positivity, k, fun x => ?_⟩
  have he : iteratedFDeriv ℝ m (fun x => f (L x + b)) x =
      (iteratedFDeriv ℝ m f (L x + b)).compContinuousLinearMap (fun _ => L) := by
    have hs : ContDiff ℝ (⊤ : ℕ∞) (fun y => f (y + b)) :=
      hfs.comp (contDiff_id.add contDiff_const)
    rw [show (fun x => f (L x + b)) = (fun y => f (y + b)) ∘ L from rfl,
      L.iteratedFDeriv_comp_right hs x (by simp), iteratedFDeriv_comp_add_right]
  have hy : 1 + ‖L x + b‖ ≤ D * (1 + ‖x‖) := by
    have hn := (norm_add_le (L x) b).trans (add_le_add (L.le_opNorm x) (le_refl ‖b‖))
    dsimp [D]
    nlinarith [norm_nonneg x, norm_nonneg L, norm_nonneg b,
      mul_nonneg (norm_nonneg b) (norm_nonneg x)]
  rw [he]
  calc
    _ ≤ ‖iteratedFDeriv ℝ m f (L x + b)‖ * ∏ _ : Fin m, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ m f (L x + b)‖ * ‖L‖ ^ m := by simp
    _ ≤ (C * (1 + ‖L x + b‖) ^ k) * ‖L‖ ^ m := by
      exact mul_le_mul_of_nonneg_right (hb _) (pow_nonneg (norm_nonneg _) _)
    _ ≤ (C * (D * (1 + ‖x‖)) ^ k) * ‖L‖ ^ m := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

theorem hasPolynomialDerivativeGrowth_norm_sq :
    HasPolynomialDerivativeGrowth (fun x : Space n => ‖x‖ ^ 2) := by
  intro m
  rcases m with _ | _ | _ | m
  · refine ⟨1, by norm_num, 2, fun x => ?_⟩
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ‖x‖), one_mul]
    nlinarith [norm_nonneg x]
  · refine ⟨2, by norm_num, 2, fun x => ?_⟩
    rw [norm_iteratedFDeriv_one, fderiv_norm_sq_apply, two_smul]
    calc
      ‖innerSL ℝ x + innerSL ℝ x‖ ≤ ‖innerSL ℝ x‖ + ‖innerSL ℝ x‖ := norm_add_le _ _
      _ = 2 * ‖x‖ := by rw [innerSL_apply_norm]; ring
      _ ≤ _ := by nlinarith [norm_nonneg x]
  · let L : Space n →L[ℝ] Space n →L[ℝ] ℝ :=
      (2 : ℝ) • (innerSL ℝ : Space n →L[ℝ] Space n →L[ℝ] ℝ)
    refine ⟨‖L‖, norm_nonneg _, 0, fun x => ?_⟩
    have hd : fderiv ℝ (fun y : Space n => ‖y‖ ^ 2) = ⇑L := by
      funext y
      rw [fderiv_norm_sq_apply]
      ext z
      simp [L]
      exact (innerSL_apply_apply ℝ y z).symm
    rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one, hd, L.fderiv]
    simp
  · refine ⟨0, le_rfl, 0, fun x => ?_⟩
    rw [iteratedFDeriv_norm_sq_eq_zero (by omega)]
    simp

theorem norm_iteratedFDeriv_tiltLogLaplace_le_of_support_ball
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hc : IsCompact μ.support) {R : ℝ} (hR : 0 ≤ R)
    (hball : μ.support ⊆ closedBall (0 : Space n) R)
    {m : ℕ} (hm : m ≠ 0) (x : Space n) :
    ‖iteratedFDeriv ℝ m (tiltLogLaplace μ) x‖ ≤ compactCumulantBound R m := by
  rw [← cumulantTensor_exponentialTilt hc hm]
  exact norm_cumulantTensor_tilted_le_of_support_ball hc hR hball (by fun_prop) m

theorem norm_tiltLogLaplace_le_of_support_ball
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hc : IsCompact μ.support) {R : ℝ} (hR : 0 ≤ R)
    (hball : μ.support ⊆ closedBall (0 : Space n) R) (x : Space n) :
    ‖tiltLogLaplace μ x‖ ≤ compactCumulantBound R 1 * ‖x‖ := by
  have hdiff : Differentiable ℝ (tiltLogLaplace μ) :=
    (contDiff_tiltLogLaplace hc).differentiable (by simp)
  have hb (z : Space n) : ‖fderiv ℝ (tiltLogLaplace μ) z‖ ≤ compactCumulantBound R 1 := by
    rw [← norm_iteratedFDeriv_one]
    exact norm_iteratedFDeriv_tiltLogLaplace_le_of_support_ball hc hR hball (by norm_num) z
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
    (s := univ) (fun z _ => hdiff z) (fun z _ => hb z) convex_univ
    (mem_univ (0 : Space n)) (mem_univ x)
  simpa [tiltLogLaplace, tiltPartition] using hh

theorem hasPolynomialDerivativeGrowth_tiltLogLaplace
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hc : IsCompact μ.support) {R : ℝ} (hR : 0 ≤ R)
    (hball : μ.support ⊆ closedBall (0 : Space n) R) :
    HasPolynomialDerivativeGrowth (tiltLogLaplace μ) := by
  intro m
  by_cases hm : m = 0
  · subst m
    refine ⟨compactCumulantBound R 1, compactCumulantBound_nonneg hR 1, 1, fun x => ?_⟩
    rw [norm_iteratedFDeriv_zero, pow_one]
    exact (norm_tiltLogLaplace_le_of_support_ball hc hR hball x).trans
      (mul_le_mul_of_nonneg_left (by linarith) (compactCumulantBound_nonneg hR 1))
  · refine ⟨compactCumulantBound R m, compactCumulantBound_nonneg hR m, 0, fun x => ?_⟩
    simpa only [pow_zero, mul_one] using
      norm_iteratedFDeriv_tiltLogLaplace_le_of_support_ball hc hR hball hm x

/-- Compact-source Gaussian potentials have polynomial growth at every
derivative order, including the potential itself and its first two derivatives. -/
theorem hasPolynomialDerivativeGrowth_gaussianSmoothedPotential
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hc : IsCompact μ.support) {r : ℝ} (hr : r ≠ 0) :
    HasPolynomialDerivativeGrowth (gaussianSmoothedPotential μ r) := by
  let V := gaussianSmoothedPotential μ r
  let a : ℝ := (r⁻¹) ^ 2
  let ν := μ.tilted (gaussianPosteriorScore r (0 : Space n))
  have hq : Continuous (gaussianPosteriorScore r (0 : Space n)) := by
    unfold gaussianPosteriorScore
    fun_prop
  have := tilted_isProbability_of_compact_support hc hq
  have hν : IsCompact ν.support := by dsimp [ν]; rwa [tilted_support_eq hc hq]
  obtain ⟨R, hR, hball⟩ := hν.isBounded.subset_closedBall_lt 0 (0 : Space n)
  have hLap := hasPolynomialDerivativeGrowth_tiltLogLaplace hν hR.le hball
  have hLs := contDiff_tiltLogLaplace hν
  have hComp : HasPolynomialDerivativeGrowth (fun z : Space n => tiltLogLaplace ν (a • z)) := by
    simpa only [_root_.smul_apply, ContinuousLinearMap.id_apply, add_zero] using
      hLap.comp_clm_add hLs (a • ContinuousLinearMap.id ℝ (Space n)) 0
  have hNorm : ContDiff ℝ (⊤ : ℕ∞) (fun z : Space n => ‖z‖ ^ 2) := contDiff_norm_sq ℝ
  have hQuad := hasPolynomialDerivativeGrowth_norm_sq.const_mul hNorm (a / 2)
  have hQuadS : ContDiff ℝ (⊤ : ℕ∞) (fun z : Space n => a / 2 * ‖z‖ ^ 2) :=
    contDiff_const.mul hNorm
  have hSum := (HasPolynomialDerivativeGrowth.const (n := n) (V 0)).add
    hQuad contDiff_const hQuadS
  have hCompS : ContDiff ℝ (⊤ : ℕ∞) (fun z : Space n => tiltLogLaplace ν (a • z)) :=
    hLs.comp (by fun_prop)
  have he : V = fun z => V 0 + a / 2 * ‖z‖ ^ 2 - tiltLogLaplace ν (a • z) := by
    funext z
    simpa only [zero_add, inner_zero_left, mul_zero, add_zero, V, ν, a] using
      gaussianSmoothedPotential_translate hc hr (0 : Space n) z
  change HasPolynomialDerivativeGrowth V
  rw [he]
  exact hSum.sub hComp (contDiff_const.add hQuadS) hCompS

theorem HasPolynomialDerivativeGrowth.comp_continuousAffineMap
    {f : Space n → ℝ} (hf : HasPolynomialDerivativeGrowth f)
    (hfs : ContDiff ℝ (⊤ : ℕ∞) f) (F : Space n →ᴬ[ℝ] Space n) :
    HasPolynomialDerivativeGrowth (fun x => f (F x)) := by
  have he : (fun x => f (F x)) = fun x => f (F.contLinear x + F 0) := by
    funext x
    congr 1
    simpa using F.map_vadd (0 : Space n) x
  rw [he]
  exact hf.comp_clm_add hfs F.contLinear (F 0)

theorem HasPolynomialDerivativeGrowth.dampedPotential
    {V : Space n → ℝ} (hV : HasPolynomialDerivativeGrowth V)
    (hVs : ContDiff ℝ (⊤ : ℕ∞) V) (μ : Measure (Space n)) (ε : ℝ) :
    HasPolynomialDerivativeGrowth (dampedPotential μ V ε) := by
  have hn : ContDiff ℝ (⊤ : ℕ∞) (fun z : Space n => ‖z‖ ^ 2) := contDiff_norm_sq ℝ
  exact (hV.add (hasPolynomialDerivativeGrowth_norm_sq.const_mul hn ε)
    hVs (contDiff_const.mul hn)).add (HasPolynomialDerivativeGrowth.const _)
      (hVs.add (contDiff_const.mul hn)) contDiff_const

theorem HasPolynomialDerivativeGrowth.affineTransformedPotential
    {V : Space n → ℝ} (hV : HasPolynomialDerivativeGrowth V)
    (hVs : ContDiff ℝ (⊤ : ℕ∞) V)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) (hA : A.det ≠ 0) :
    HasPolynomialDerivativeGrowth (affineTransformedPotential V A b hA) := by
  exact (hV.comp_continuousAffineMap hVs
    (affineMatrixEquiv A b hA).symm.toContinuousAffineMap).sub
      (HasPolynomialDerivativeGrowth.const _)
      (hVs.comp (affineMatrixEquiv A b hA).symm.toContinuousAffineMap.contDiff) contDiff_const

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.hasPolynomialDerivativeGrowth_norm_sq
#print axioms KLS.DeterministicBridgeIntegration.hasPolynomialDerivativeGrowth_tiltLogLaplace
#print axioms KLS.DeterministicBridgeIntegration.hasPolynomialDerivativeGrowth_gaussianSmoothedPotential
#print axioms KLS.DeterministicBridgeIntegration.HasPolynomialDerivativeGrowth.dampedPotential
#print axioms KLS.DeterministicBridgeIntegration.HasPolynomialDerivativeGrowth.affineTransformedPotential

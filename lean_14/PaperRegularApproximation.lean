import HessianUpperBoundTransform
import KLS.FullPoincareStrongApproximation
import KLS.FaithfulFullTaylorCriterion

/-! Actual-law approximation by the paper's narrower regular class.
All regularity properties are proved for the released cutoff, Gaussian,
damping and whitening construction. The transfer theorem retains precisely
the still-unproved spectral inequality on regular isotropic laws. -/

open MeasureTheory InnerProductSpace Set Filter Metric Matrix
open scoped ENNReal ContDiff Topology RealInnerProductSpace BigOperators NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ}

def HasPaperRegularDensity (μ : Measure (Space n)) : Prop :=
  ∃ (V : Space n → ℝ) (κ : ℝ), ContDiff ℝ (⊤ : ℕ∞) V ∧
    0 < κ ∧ StrongConvexOn univ κ V ∧ HasHessianUpperBound V ∧
      HasPolynomialDerivativeGrowth V ∧ μ = potentialMeasure V

theorem HasPaperRegularDensity.to_smoothStronglyConvexDensity
    {μ : Measure (Space n)} (hμ : HasPaperRegularDensity μ) :
    HasSmoothStronglyConvexDensity μ := by
  obtain ⟨V, κ, hV, hκ, hc, _, _, heq⟩ := hμ
  exact ⟨V, κ, hV, hκ, hc, heq⟩

theorem HasPolynomialDerivativeGrowth.scalarTransformedPotential
    {V : Space n → ℝ} (hV : HasPolynomialDerivativeGrowth V)
    (hVs : ContDiff ℝ (⊤ : ℕ∞) V) (a : ℝ) :
    HasPolynomialDerivativeGrowth (scalarTransformedPotential V a) := by
  have hp : HasPolynomialDerivativeGrowth (fun x : Space n => V (a⁻¹ • x)) := by
    simpa only [_root_.smul_apply, ContinuousLinearMap.id_apply, add_zero] using
      hV.comp_clm_add hVs (a⁻¹ • ContinuousLinearMap.id ℝ (Space n)) 0
  exact hp.sub (HasPolynomialDerivativeGrowth.const _)
    (hVs.comp (by fun_prop)) contDiff_const

theorem HasHessianUpperBound.scalarTransformedPotential
    {V : Space n → ℝ} (hV : HasHessianUpperBound V)
    (hVs : ContDiff ℝ 2 V) (a : ℝ) :
    HasHessianUpperBound (scalarTransformedPotential V a) := by
  have hp : HasHessianUpperBound (fun x : Space n => V (a⁻¹ • x)) := by
    simpa only [_root_.smul_apply, ContinuousLinearMap.id_apply, add_zero] using
      hV.comp_clm_add hVs (a⁻¹ • ContinuousLinearMap.id ℝ (Space n)) 0
  exact hp.sub_const (hVs.comp (by fun_prop)) _

/-- The actual damped and affinely whitened law has every paper regularity
property, provided those already-proved analytic properties hold for V. -/
theorem affine_quadraticDamping_paperRegularDensity
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] {V : Space n → ℝ}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hc : ConvexOn ℝ univ V)
    (heq : μ = potentialMeasure V) (hupper : HasHessianUpperBound V)
    (hgrowth : HasPolynomialDerivativeGrowth V) {ε : ℝ} (hε : 0 < ε)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) (hA : A.det ≠ 0) :
    HasPaperRegularDensity (affineMatrixMeasure (quadraticDamping μ ε) A b) := by
  let W := dampedPotential μ V ε
  have hW : ContDiff ℝ (⊤ : ℕ∞) W := dampedPotential_contDiff hV ε
  refine ⟨affineTransformedPotential W A b hA,
    (2 * ε) / (‖matrixAction A‖ + 1) ^ 2,
    affineTransformedPotential_contDiff hW A b hA, by positivity,
    affineTransformedPotential_strongConvex (by positivity) (dampedPotential_strongConvex hc ε)
      A b hA,
    (hupper.dampedPotential (hV.of_le (by simp)) μ hε.le).affineTransformedPotential
      (hW.of_le (by simp)) A b hA,
    (hgrowth.dampedPotential hV μ ε).affineTransformedPotential hW A b hA, ?_⟩
  change (quadraticDamping μ ε).map (affineMatrixEquiv A b hA) = _
  rw [quadraticDamping_eq_potentialMeasure_nonneg hV.continuous.measurable heq hε.le,
    map_potentialMeasure_affineMatrixEquiv hW.continuous.measurable]

theorem eventually_admissible_paperRegularDensity_whitened_damping
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {ε : ℕ → ℝ} (hε : ∀ k, 0 ≤ ε k) (hεlim : Tendsto ε atTop (𝓝 0))
    {V : Space n → ℝ} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hc : ConvexOn ℝ univ V) (heq : μ = potentialMeasure V)
    (hupper : HasHessianUpperBound V) (hgrowth : HasPolynomialDerivativeGrowth V)
    (hpos : ∀ k, 0 < ε k) :
    ∀ᶠ k in atTop, admissibleMeasure (whitenedMeasure (quadraticDamping μ (ε k))) ∧
      HasPaperRegularDensity (whitenedMeasure (quadraticDamping μ (ε k))) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  filter_upwards [eventually_posDef_covarianceMatrix_quadraticDamping_nonneg hμ hε hεlim] with k hk
  let : IsProbabilityMeasure (quadraticDamping μ (ε k)) :=
    isProbabilityMeasure_quadraticDamping_nonneg μ (hε k)
  refine ⟨⟨inferInstance,
    (measureLogConcave_quadraticDamping_of_potential hV hc heq (hε k)).whitenedMeasure,
    whitenedMeasure_isIsotropic (hμ.isotropic.memLp_id_quadraticDamping_nonneg (hε k)) hk⟩, ?_⟩
  exact affine_quadraticDamping_paperRegularDensity hV hc heq hupper hgrowth (hpos k) _ _
    (inverseSqrtMatrix_det_ne_zero hk)

theorem mem_poincareConstants_of_paperRegularDensity_of_smooth_global
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {V : Space n → ℝ} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hc : ConvexOn ℝ univ V)
    (heq : μ = potentialMeasure V) (hupper : HasHessianUpperBound V)
    (hgrowth : HasPolynomialDerivativeGrowth V) {C : ℝ≥0} (hC : 0 < C)
    (hregular : ∀ ν : Measure (Space n), admissibleMeasure ν →
      HasPaperRegularDensity ν → C ∈ poincareConstants ν) :
    C ∈ poincareConstants μ := by
  let : IsProbabilityMeasure μ := hμ.isProb
  let ν := fun k => quadraticDamping μ (cutoffScale k)
  let : ∀ k, IsProbabilityMeasure (ν k) := fun k =>
    isProbabilityMeasure_quadraticDamping_nonneg μ (cutoffScale_pos k).le
  let : ∀ k, IsProbabilityMeasure (whitenedMeasure (ν k)) := fun _ => inferInstance
  apply mem_poincareConstants_of_weak_measure_limit hμ.absolutelyContinuousLebesgue hC
    (ν := fun k => whitenedMeasure (ν k))
  · filter_upwards [eventually_admissible_paperRegularDensity_whitened_damping hμ
      (fun k => (cutoffScale_pos k).le) cutoffScale_tendsto_zero hV hc heq
      hupper hgrowth cutoffScale_pos] with k hk
    exact hregular _ hk.1 hk.2
  · exact fun _ hf hs => hμ.tendsto_integral_whitened_quadraticDamping_compact
      (fun k => (cutoffScale_pos k).le) cutoffScale_tendsto_zero hf hs

/-- The narrower paper regular class suffices for the full faithful class.
The approximation is completely discharged; the only inequality premise is
the desired bound on actual regular isotropic probability laws. -/
theorem mem_poincareConstants_of_paperRegularDensity
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) {C : ℝ≥0} (hC : 0 < C)
    (hregular : ∀ ν : Measure (Space n), admissibleMeasure ν →
      HasPaperRegularDensity ν → C ∈ poincareConstants ν) :
    C ∈ poincareConstants μ := by
  apply hμ.mem_poincareConstants_of_compact_laws hC
  intro ρ hρ hs
  let : IsProbabilityMeasure ρ := hρ.isProb
  apply mem_poincareConstants_of_isotropicGaussianSmoothing hρ.absolutelyContinuousLebesgue hC
  refine Eventually.of_forall fun k => ?_
  have hr := (cutoffScale_pos k).ne'
  have hGauss := gaussianSmoothedPotential_contDiff hs hr
  have hupper : HasHessianUpperBound (isotropicGaussianPotential ρ (cutoffScale k)) :=
    (hasHessianUpperBound_gaussianSmoothedPotential hs hr).scalarTransformedPotential
      (hGauss.of_le (by simp)) _
  have hgrowth : HasPolynomialDerivativeGrowth (isotropicGaussianPotential ρ (cutoffScale k)) :=
    (hasPolynomialDerivativeGrowth_gaussianSmoothedPotential hs hr).scalarTransformedPotential hGauss _
  exact mem_poincareConstants_of_paperRegularDensity_of_smooth_global
    (hρ.isotropicGaussianSmoothing hr)
    (isotropicGaussianPotential_contDiff hs hr)
    (hρ.isotropicGaussianPotential_convex hs hr)
    (hρ.isotropicGaussianSmoothing_eq_exp_potential hs hr) hupper hgrowth hC hregular

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.affine_quadraticDamping_paperRegularDensity
#print axioms KLS.DeterministicBridgeIntegration.eventually_admissible_paperRegularDensity_whitened_damping
#print axioms KLS.DeterministicBridgeIntegration.mem_poincareConstants_of_paperRegularDensity

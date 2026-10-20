import KLSConstantImprovement.ActualGlobalRawFormTest405
import KLSConstantImprovement.ActualRawPoissonIdentification405
import KLSConstantImprovement.ActualSourceRegularizedFluxDivergence405
import KLSConstantImprovement.ActualSourceBoundedMassCutoffs405
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Actual global generator membership of smooth target pullbacks.
Their generator and the natural inverse are identified by genuine weak
source calculus and the accepted form uniqueness theorem. This supplies
the concrete bounded-mass generator test class; it does not assert that
its generator range is dense in source L2. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualTargetPullbackGenerator405
open KLS ActualBoundedCanonicalSource ActualGlobalRawFormTest405
open ActualSourcePullbackMetricGradient405 ActualBoundedRawSourceCalculus405
open ActualBoundedRawTestAlgebra405 ActualRawPoissonIdentification405
open ActualSourceRegularizedFluxDivergence405 ActualWeakSourceCompactVectorBochner
open ActualCompactWeakSourceVectorSquare ActualCompactWeakSourceVectorBochner
open ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricInverse
open ActualSourceBoundedMassCutoffs405
open ActualCompactRawMetricGraph ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

def targetPullbackGenerator (d : SourceData μ) (f : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i : Fin n, (gradient d.potential x i * coordinateDerivative f i (gradient d.potential x) -
    pullbackRawGradient d (coordinateDerivative f i) i x)

theorem targetPullbackGenerator_memLp_top (d : SourceData μ)
    {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) :
    MemLp (targetPullbackGenerator d f) ∞ (potentialMeasure d.potential) := by
  apply memLp_finsetSum Finset.univ
  intro i _
  have hfi : ContDiff ℝ 1 (coordinateDerivative f i) :=
    contDiff_coordinateDerivative hf (m := 1) (by norm_num) i
  have hX := d.continuous_comp_gradient_memLp (EuclideanSpace.proj i).continuous ∞
  have hv := d.continuous_comp_gradient_memLp hfi.continuous ∞
  have hd := d.pullback_weak_derivative_memLp hfi i ∞
  exact (hX.mul hv).sub hd

theorem integral_targetPullbackGenerator_eq_zero (d : SourceData μ)
    {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) :
    (∫ x, targetPullbackGenerator d f x ∂potentialMeasure d.potential) = 0 := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hfi (i : Fin n) : ContDiff ℝ 1 (coordinateDerivative f i) :=
    contDiff_coordinateDerivative hf (m := 1) (by norm_num) i
  have hv (i : Fin n) := d.continuous_comp_gradient_memLp (hfi i).continuous 2
  have hX (i : Fin n) := d.continuous_comp_gradient_memLp (EuclideanSpace.proj i).continuous 2
  have hp (i : Fin n) : Integrable (fun x => gradient d.potential x i *
      coordinateDerivative f i (gradient d.potential x)) (potentialMeasure d.potential) :=
    (hX i).integrable_mul (hv i)
  have hd (i : Fin n) : Integrable (pullbackRawGradient d (coordinateDerivative f i) i)
      (potentialMeasure d.potential) :=
    (d.pullback_weak_derivative_memLp (hfi i) i 2).integrable (by norm_num)
  have hI (i : Fin n) : Integrable (fun x => gradient d.potential x i *
      coordinateDerivative f i (gradient d.potential x) -
        pullbackRawGradient d (coordinateDerivative f i) i x) (potentialMeasure d.potential) := by
    have hi := (hp i).sub (hd i)
    change Integrable (fun x => gradient d.potential x i *
      coordinateDerivative f i (gradient d.potential x) -
        pullbackRawGradient d (coordinateDerivative f i) i x) (potentialMeasure d.potential) at hi
    exact hi
  unfold targetPullbackGenerator
  rw [integral_finsetSum Finset.univ (fun i _ => hI i)]
  apply Finset.sum_eq_zero
  intro i _
  have hsplit : (∫ x, gradient d.potential x i * coordinateDerivative f i (gradient d.potential x) -
      pullbackRawGradient d (coordinateDerivative f i) i x ∂potentialMeasure d.potential) =
      (∫ x, gradient d.potential x i * coordinateDerivative f i (gradient d.potential x)
        ∂potentialMeasure d.potential) -
      ∫ x, pullbackRawGradient d (coordinateDerivative f i) i x ∂potentialMeasure d.potential :=
    integral_sub (hp i) (hd i)
  rw [hsplit]
  have hs := ActualBoundedRawSourceCalculus405.BoundedRawTest.global_source_stein
    (pullbackTest d (coordinateDerivative f i) (hfi i)) i
  change (∫ x, pullbackRawGradient d (coordinateDerivative f i) i x ∂potentialMeasure d.potential) =
    ∫ x, coordinateDerivative f i (gradient d.potential x) * gradient d.potential x i
      ∂potentialMeasure d.potential at hs
  have hc : (∫ x, gradient d.potential x i * coordinateDerivative f i (gradient d.potential x)
      ∂potentialMeasure d.potential) =
      ∫ x, coordinateDerivative f i (gradient d.potential x) * gradient d.potential x i
        ∂potentialMeasure d.potential :=
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  rw [hc, hs]
  exact sub_self _

def targetPullbackGeneratorLp (d : SourceData μ) (f : Space n → ℝ) (hf : ContDiff ℝ 2 f) :
    Lp ℝ 2 (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  exact ((targetPullbackGenerator_memLp_top d hf).mono_exponent (by simp)).toLp
    (targetPullbackGenerator d f)

theorem targetPullbackGeneratorLp_coe (d : SourceData μ)
    {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) :
    (targetPullbackGeneratorLp d f hf : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      targetPullbackGenerator d f := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  exact ((targetPullbackGenerator_memLp_top d hf).mono_exponent (by simp)).coeFn_toLp

theorem integral_targetPullbackGeneratorLp_eq_zero (d : SourceData μ)
    {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) :
    (∫ x, targetPullbackGeneratorLp d f hf x ∂potentialMeasure d.potential) = 0 := by
  rw [integral_congr_ae (targetPullbackGeneratorLp_coe d hf)]
  exact integral_targetPullbackGenerator_eq_zero d hf

theorem pullback_inverse_hessian_compact_pair (d : SourceData μ) (f : Space n → ℝ)
    (ψ : Space n → ℝ) :
    (fun x => ∑ a : Fin n, ∑ b : Fin n, (coordinateHessian d.potential x)⁻¹ a b *
      pullbackRawGradient d f a x * coordinateDerivative ψ b x)
      =ᵐ[potentialMeasure d.potential]
        (fun x => ∑ b : Fin n, coordinateDerivative f b (gradient d.potential x) *
          coordinateDerivative ψ b x) := by
  filter_upwards [d.hessian_ae_source] with x hp
  let H := coordinateHessian d.potential x
  let v := gradient f (gradient d.potential x)
  have hF : (fun a => pullbackRawGradient d f a x) = H *ᵥ (fun a => v a) := by
    funext a
    have he := inner_matrixAction_transpose H v (EuclideanSpace.single a 1)
    rw [hp.1.isHermitian.isSymm.eq] at he
    change inner ℝ v (matrixAction H (EuclideanSpace.single a 1)) = _
    rw [← he, EuclideanSpace.inner_single_right]
    simp [matrixAction_apply, Matrix.mulVec, dotProduct]
  have hJF : H⁻¹ *ᵥ (fun a => pullbackRawGradient d f a x) = (fun a => v a) := by
    rw [hF, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul H
      ((Matrix.isUnit_iff_isUnit_det H).mp hp.1.isUnit), Matrix.one_mulVec]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  calc
    _ = (∑ a : Fin n, H⁻¹ b a * pullbackRawGradient d f a x) * coordinateDerivative ψ b x := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      have hJ : Matrix.IsSymm (H⁻¹) := hp.1.inv.isHermitian.isSymm
      rw [hJ.apply a b]
    _ = _ := by
      have he := congrFun hJF b
      change (∑ a : Fin n, H⁻¹ b a * pullbackRawGradient d f a x) = v b at he
      rw [he]
      simp only [v, coordinateDerivative_eq_gradient]

theorem targetPullbackGenerator_compact_equation (d : SourceData μ)
    {f : Space n → ℝ} (hf : ContDiff ℝ 2 f)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    (∫ x, ∑ a : Fin n, ∑ b : Fin n, (coordinateHessian d.potential x)⁻¹ a b *
      pullbackRawGradient d f a x * coordinateDerivative ψ b x ∂potentialMeasure d.potential) =
      ∫ x, targetPullbackGeneratorLp d f hf x * ψ x ∂potentialMeasure d.potential := by
  let u : Fin n → Space n → ℝ := fun i x => coordinateDerivative f i (gradient d.potential x)
  let Du : Fin n → Fin n → Space n → ℝ := fun i j => pullbackRawGradient d (coordinateDerivative f i) j
  have hfi (i : Fin n) : ContDiff ℝ 1 (coordinateDerivative f i) :=
    contDiff_coordinateDerivative hf (m := 1) (by norm_num) i
  have hu (i : Fin n) : MemLp (u i) 2 (potentialMeasure d.potential) :=
    d.continuous_comp_gradient_memLp (hfi i).continuous 2
  have hDu (i j : Fin n) (E : Set (Space n)) (hE : IsCompact E) : MemLp (Du i j) 2 (volume.restrict E) :=
    KLS.MemLp.restrict_volume_of_potentialMeasure
      (d.pullback_weak_derivative_memLp (hfi i) j 2) d.source_C1.continuous hE
  have hw (i j : Fin n) : HasLocalWeakCoordinateDerivative (u i) (Du i j) j :=
    d.pullback_hasLocalWeakCoordinateDerivative (hfi i) j
  have hp := raw_vector_source_adjoint_compact_pair d u Du hu hDu hw (hψ.of_le (by simp)) hc
  have hδ : rawWeakSourceVectorAdjoint d.potential u Du = targetPullbackGenerator d f := by
    funext x
    simp only [rawWeakSourceVectorAdjoint, rawWeakSourceAdjoint, targetPullbackGenerator,
      coordinateDerivative_eq_gradient, u, Du]
  rw [hδ] at hp
  have hi (i : Fin n) : Integrable (fun x => u i x * coordinateDerivative ψ i x)
      (potentialMeasure d.potential) :=
    (hu i).integrable_mul (memLp_of_continuous_hasCompactSupport d.source_C1.continuous
      (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous
      (hasCompactSupport_coordinateDerivative hc i))
  calc
    _ = ∫ x, ∑ b : Fin n, u b x * coordinateDerivative ψ b x ∂potentialMeasure d.potential :=
      integral_congr_ae (pullback_inverse_hessian_compact_pair d f ψ)
    _ = ∑ b : Fin n, ∫ x, u b x * coordinateDerivative ψ b x ∂potentialMeasure d.potential :=
      integral_finsetSum Finset.univ (fun i _ => hi i)
    _ = ∫ x, targetPullbackGenerator d f x * ψ x ∂potentialMeasure d.potential := hp.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [targetPullbackGeneratorLp_coe d hf] with x hx
      rw [hx]

theorem natural_inverse_of_targetPullbackGenerator (d : SourceData μ)
    {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) :
    (sourceMetricInverse d (targetPullbackGeneratorLp d f hf) : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential]
        (fun x => f (gradient d.potential x) - ∫ y, f (gradient d.potential y) ∂potentialMeasure d.potential) ∧
      ∀ i, (canonicalMetricGradient d.potential i
        (sourceMetricInverseH1 d (targetPullbackGeneratorLp d f hf)) : Space n → ℝ)
        =ᵐ[potentialMeasure d.potential] rawCanonicalMetricDerivative d.potential (pullbackRawGradient d f) i := by
  let T := pullbackTest d f (hf.of_le (by simp))
  have he : Integrable (rawInverseHessianGradientForm d.potential T.derivative)
      (potentialMeasure d.potential) :=
    (integrable_finsetSum Finset.univ (fun i _ => (T.metric_gradient i).integrable_sq)).congr
      (d.raw_metric_derivative_sq_ae T.derivative)
  exact exists_actual_inverse_of_raw_compact_equation d (targetPullbackGeneratorLp d f hf)
    (integral_targetPullbackGeneratorLp_eq_zero d hf)
    (d.continuous_comp_gradient_memLp hf.continuous 2) T.derivative_local T.weak_derivative he
    (fun ψ hψ hc => targetPullbackGenerator_compact_equation d hf hψ hc)

/-- Every actual generator datum from a smooth global target pullback has
bounded natural inverse mass. No mass or graph-core premise is supplied. -/
theorem exists_mass_bound_targetPullbackGenerator (d : SourceData μ)
    {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (targetPullbackGeneratorLp d f hf)) x ≤ C := by
  let g := targetPullbackGeneratorLp d f hf
  have hg (i : Fin n) : MemLp (canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g)) ∞
      (potentialMeasure d.potential) :=
    (memLp_congr_ae ((natural_inverse_of_targetPullbackGenerator d hf).2 i)).mpr
      (pullback_raw_metric_gradient_memLp_top d (hf.of_le (by simp)) i)
  have hs : MemLp (fun x => ∑ i : Fin n,
      canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g) x ^ 2) ∞
      (potentialMeasure d.potential) := by
    apply memLp_finsetSum Finset.univ
    intro i _
    have hm : MemLp (fun x => canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g) x *
        canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g) x) ∞
        (potentialMeasure d.potential) := (hg i).mul (hg i)
    simpa only [pow_two] using hm
  have hm : MemLp (sourceVectorMass d.potential (naturalCanonicalFlux d g)) ∞
      (potentialMeasure d.potential) :=
    (memLp_congr_ae (naturalCanonicalMass_square_ae d g)).mp hs
  refine ⟨lpNorm (sourceVectorMass d.potential (naturalCanonicalFlux d g)) ∞
    (potentialMeasure d.potential), lpNorm_nonneg, ?_⟩
  filter_upwards [ae_le_lpNorm_exponent_top hm] with x hx
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hx)

end KLSConstantImprovement.ActualTargetPullbackGenerator405
#print axioms KLSConstantImprovement.ActualTargetPullbackGenerator405.targetPullbackGenerator_memLp_top
#print axioms KLSConstantImprovement.ActualTargetPullbackGenerator405.integral_targetPullbackGenerator_eq_zero
#print axioms KLSConstantImprovement.ActualTargetPullbackGenerator405.targetPullbackGeneratorLp_coe
#print axioms KLSConstantImprovement.ActualTargetPullbackGenerator405.integral_targetPullbackGeneratorLp_eq_zero
#print axioms KLSConstantImprovement.ActualTargetPullbackGenerator405.pullback_inverse_hessian_compact_pair
#print axioms KLSConstantImprovement.ActualTargetPullbackGenerator405.targetPullbackGenerator_compact_equation
#print axioms KLSConstantImprovement.ActualTargetPullbackGenerator405.natural_inverse_of_targetPullbackGenerator
#print axioms KLSConstantImprovement.ActualTargetPullbackGenerator405.exists_mass_bound_targetPullbackGenerator

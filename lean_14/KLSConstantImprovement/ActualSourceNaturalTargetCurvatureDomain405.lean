import KLSConstantImprovement.ActualSourceConnectionFields405
import KLSConstantImprovement.ActualSourceGradientCoefficientPassage405

/-! The target-curvature contraction of the actual natural inverse is
already globally L1 from its ordinary gradient. No bounded natural mass
or connection domain is assumed. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff NNReal ENNReal
namespace KLSConstantImprovement.ActualSourceNaturalTargetCurvatureDomain405
open KLS ActualBoundedCanonicalSource ActualSourceConnectionFields405 ActualSourceCurvatureDomains405
open ActualSourceNaturalGaffney405 ActualSourceLimitFluxDomains405 ActualSourceGradientCoefficientPassage405
open ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricInverse ActualWeakCanonicalMetricOrdinaryGraph
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

def naturalCanonicalRawGradient (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (i : Fin n) (x : Space n) : ℝ :=
  ∑ a : Fin n, canonicalMetricUnroot d.potential x i a *
    canonicalMetricGradient d.potential a (sourceMetricInverseH1 d g) x

theorem naturalCanonicalRawGradient_memLp (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (i : Fin n) :
    MemLp (naturalCanonicalRawGradient d g i) 2 (potentialMeasure d.potential) :=
  memLp_finsetSum Finset.univ fun a _ => (actualUnroot_entry_memLp_top d i a).mul (Lp.memLp _)

theorem hessian_mul_naturalCanonicalFlux_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      coordinateHessian d.potential x *ᵥ (fun i => naturalCanonicalFlux d g i x) =
        (fun i => naturalCanonicalRawGradient d g i x) := by
  filter_upwards [d.hessian_ae_source] with x hp
  change coordinateHessian d.potential x *ᵥ
    (canonicalMetricRoot d.potential x *ᵥ
      (fun a => canonicalMetricGradient d.potential a (sourceMetricInverseH1 d g) x)) = _
  rw [Matrix.mulVec_mulVec, hessian_mul_canonicalMetricRoot_at hp.1]
  rfl

theorem natural_targetCurvature_eq_rawGradient_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    sourceConnectionTarget d (naturalCanonicalFlux d g) =ᵐ[potentialMeasure d.potential]
      fun x => ∑ i : Fin n, ∑ j : Fin n,
        coordinateHessian d.targetPotential (gradient d.potential x) i j *
          naturalCanonicalRawGradient d g i x * naturalCanonicalRawGradient d g j x := by
  filter_upwards [d.hessian_ae_source, hessian_mul_naturalCanonicalFlux_ae d g] with x hp hHu
  let H := coordinateHessian d.potential x
  let V := coordinateHessian d.targetPotential (gradient d.potential x)
  let u : Fin n → ℝ := fun i => naturalCanonicalFlux d g i x
  have hd (v : Fin n → ℝ) : u ⬝ᵥ (H *ᵥ v) = (H *ᵥ u) ⬝ᵥ v := by
    have he := Matrix.dotProduct_transpose_mulVec H u v
    rw [hp.1.isHermitian.isSymm.eq] at he
    exact he.trans (dotProduct_comm v (H *ᵥ u))
  calc
    _ = u ⬝ᵥ ((H * V * H) *ᵥ u) := matrix_quadratic_sum_eq_dotProduct _ _
    _ = u ⬝ᵥ (H *ᵥ (V *ᵥ (H *ᵥ u))) := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = (H *ᵥ u) ⬝ᵥ (V *ᵥ (H *ᵥ u)) := hd _
    _ = _ := by rw [hHu]; exact (matrix_quadratic_sum_eq_dotProduct _ _).symm

theorem natural_targetCurvature_integrable (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) :
    Integrable (sourceConnectionTarget d (naturalCanonicalFlux d g)) (potentialMeasure d.potential) := by
  have hV2 : ContDiff ℝ 2 d.targetPotential := d.target_smooth.of_le (by simp)
  have hV (i j : Fin n) : MemLp
      (fun x => coordinateHessian d.targetPotential (gradient d.potential x) i j) ∞
      (potentialMeasure d.potential) :=
    d.continuous_comp_gradient_memLp
      (contDiff_coordinateHessian hV2 (m := 0) (by norm_num) i j).continuous ∞
  have hi : Integrable (fun x => ∑ i : Fin n, ∑ j : Fin n,
      coordinateHessian d.targetPotential (gradient d.potential x) i j *
        naturalCanonicalRawGradient d g i x * naturalCanonicalRawGradient d g j x)
      (potentialMeasure d.potential) := by
    apply integrable_finsetSum Finset.univ
    intro i _
    apply integrable_finsetSum Finset.univ
    intro j _
    have hp : MemLp (fun x => coordinateHessian d.targetPotential (gradient d.potential x) i j *
        naturalCanonicalRawGradient d g i x) 2 (potentialMeasure d.potential) :=
      (hV i j).mul (naturalCanonicalRawGradient_memLp d g i)
    exact hp.integrable_mul (naturalCanonicalRawGradient_memLp d g j)
  exact hi.congr (natural_targetCurvature_eq_rawGradient_ae d g).symm

end KLSConstantImprovement.ActualSourceNaturalTargetCurvatureDomain405
#print axioms KLSConstantImprovement.ActualSourceNaturalTargetCurvatureDomain405.naturalCanonicalRawGradient_memLp
#print axioms KLSConstantImprovement.ActualSourceNaturalTargetCurvatureDomain405.hessian_mul_naturalCanonicalFlux_ae
#print axioms KLSConstantImprovement.ActualSourceNaturalTargetCurvatureDomain405.natural_targetCurvature_eq_rawGradient_ae
#print axioms KLSConstantImprovement.ActualSourceNaturalTargetCurvatureDomain405.natural_targetCurvature_integrable

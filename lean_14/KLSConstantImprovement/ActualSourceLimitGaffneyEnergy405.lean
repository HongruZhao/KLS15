import KLSConstantImprovement.ActualSourceLimitJacobianSymmetry405
import KLSConstantImprovement.ActualSourceJacobianCompactPairing405
import KLSConstantImprovement.ActualSourceGradientCoefficientPassage405

/-! The combined weak energy limit retains the actual source mass and
compatible Jacobian energy together.  Their literal sum is the squared
norm of the single limit field, so no estimate is lost by separate limits. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceLimitGaffneyEnergy405
open KLS ActualBoundedCanonicalSource ActualSourceRegularizedEnergyVector405
open ActualSourceLimitFluxDomains405 ActualSourceLimitJacobianSymmetry405
open ActualSourceJacobianCompactPairing405 ActualSourceGradientCoefficientPassage405
open ActualSourceLocalizedGaffney405 ActualCompactWeakSourceVectorSquare
open ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricOrdinaryGraph ActualSourceMetricFaithfulness405
open ActualWhitenedJacobianEnergy405
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

def energyLimitJacobianMatrix (d : SourceData μ) (V : GaffneyEnergyAmbient d) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => energyLimitJacobian d V i j x

theorem energyLimitJacobianMatrix_eq_root_sandwich (d : SourceData μ) (V : GaffneyEnergyAmbient d)
    (x : Space n) :
    energyLimitJacobianMatrix d V x = canonicalMetricRoot d.potential x *
      energyLimitWhitenedJacobian d V x * canonicalMetricUnroot d.potential x := by
  ext i j
  exact (root_sandwich_entry (canonicalMetricRoot d.potential x) (energyLimitWhitenedJacobian d V x)
    (canonicalMetricUnroot d.potential x) i j).symm

theorem energyLimitJacobian_compatible_ae (d : SourceData μ) (V : GaffneyEnergyAmbient d)
    (hZ : ∀ᵐ x ∂(volume : Measure (Space n)), (energyLimitWhitenedJacobian d V x).IsSymm) :
    ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * energyLimitJacobianMatrix d V x).IsSymm := by
  filter_upwards [d.hessian_ae, hZ] with x hp hz
  simp only [energyLimitJacobianMatrix_eq_root_sandwich, ← Matrix.mul_assoc,
    hessian_mul_canonicalMetricRoot_at hp.1]
  have hs : (canonicalMetricUnroot d.potential x).IsSymm :=
    (inverseSqrtMatrix_isSymm (coordinateHessian d.potential x)).inv
  change (canonicalMetricUnroot d.potential x * energyLimitWhitenedJacobian d V x *
    canonicalMetricUnroot d.potential x).transpose = _
  simp only [Matrix.transpose_mul, hs.eq, hz.eq, Matrix.mul_assoc]

theorem energyLimitFlux_mass_square_ae (d : SourceData μ) (V : GaffneyEnergyAmbient d) :
    (fun x => ∑ i : Fin n, V (Sum.inl i) x ^ 2) =ᵐ[potentialMeasure d.potential]
      sourceVectorMass d.potential (energyLimitFlux d V) := by
  filter_upwards [d.hessian_ae_source] with x hx
  let S := canonicalMetricUnroot d.potential x
  let u : Fin n → ℝ := fun i => energyLimitFlux d V i x
  let v : Fin n → ℝ := fun i => V (Sum.inl i) x
  have hu : S *ᵥ u = v := by
    change canonicalMetricUnroot d.potential x *ᵥ (canonicalMetricRoot d.potential x *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, canonicalMetricUnroot_mul_root_at hx.1, Matrix.one_mulVec]
  have he : (S *ᵥ u) ⬝ᵥ (S *ᵥ u) = u ⬝ᵥ (coordinateHessian d.potential x *ᵥ u) := by
    rw [← Matrix.dotProduct_transpose_mulVec S u (S *ᵥ u), Matrix.mulVec_mulVec,
      canonicalMetricUnroot_gram_at hx.1]
  calc
    _ = v ⬝ᵥ v := by simp only [v, dotProduct, pow_two]
    _ = (S *ᵥ u) ⬝ᵥ (S *ᵥ u) := by rw [hu]
    _ = _ := he
    _ = _ := (matrix_quadratic_sum_eq_dotProduct (coordinateHessian d.potential x) u).symm

theorem energyLimitJacobian_square_ae (d : SourceData μ) (V : GaffneyEnergyAmbient d)
    (hZ : ∀ᵐ x ∂(volume : Measure (Space n)), (energyLimitWhitenedJacobian d V x).IsSymm) :
    (fun x => ∑ i : Fin n, ∑ j : Fin n, V (Sum.inr (i, j)) x ^ 2)
      =ᵐ[potentialMeasure d.potential] sourceVectorJacobianEnergy (energyLimitJacobian d V) := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source, (energyLimitJacobian_compatible_ae d V hZ).filter_mono hac.ae_le]
    with x hp hc
  have hw : whitenedJacobian (coordinateHessian d.potential x) (energyLimitJacobianMatrix d V x) =
      energyLimitWhitenedJacobian d V x := by
    rw [energyLimitJacobianMatrix_eq_root_sandwich]
    change canonicalMetricUnroot d.potential x *
      (canonicalMetricRoot d.potential x * energyLimitWhitenedJacobian d V x * canonicalMetricUnroot d.potential x) *
        canonicalMetricRoot d.potential x = energyLimitWhitenedJacobian d V x
    calc
      _ = (canonicalMetricUnroot d.potential x * canonicalMetricRoot d.potential x) *
          energyLimitWhitenedJacobian d V x *
          (canonicalMetricUnroot d.potential x * canonicalMetricRoot d.potential x) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [canonicalMetricUnroot_mul_root_at hp.1, Matrix.one_mul, Matrix.mul_one]
  have hf := whitenedJacobian_frobenius (coordinateHessian d.potential x) (energyLimitJacobianMatrix d V x) hp.1 hc
  rw [hw] at hf
  simpa only [matrixFrobeniusSq, energyLimitWhitenedJacobian, energyLimitJacobianMatrix,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, sourceVectorJacobianEnergy] using hf

theorem energyLimitGaffney_integrable (d : SourceData μ) (V : GaffneyEnergyAmbient d)
    (hZ : ∀ᵐ x ∂(volume : Measure (Space n)), (energyLimitWhitenedJacobian d V x).IsSymm) :
    Integrable (sourceVectorMass d.potential (energyLimitFlux d V)) (potentialMeasure d.potential) ∧
      Integrable (sourceVectorJacobianEnergy (energyLimitJacobian d V)) (potentialMeasure d.potential) := by
  constructor
  · exact (integrable_finsetSum Finset.univ
      (fun i _ => (Lp.memLp (V (Sum.inl i))).integrable_sq)).congr (energyLimitFlux_mass_square_ae d V)
  · exact (integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => (Lp.memLp (V (Sum.inr (i, j)))).integrable_sq))).congr
      (energyLimitJacobian_square_ae d V hZ)

theorem energyLimitGaffney_integral_eq_norm_sq (d : SourceData μ) (V : GaffneyEnergyAmbient d)
    (hZ : ∀ᵐ x ∂(volume : Measure (Space n)), (energyLimitWhitenedJacobian d V x).IsSymm) :
    (∫ x, sourceVectorMass d.potential (energyLimitFlux d V) x +
      sourceVectorJacobianEnergy (energyLimitJacobian d V) x ∂potentialMeasure d.potential) = ‖V‖ ^ 2 := by
  have he : (fun x => ∑ a : GaffneyEnergyIndex n, V a x ^ 2) =ᵐ[potentialMeasure d.potential]
      (fun x => sourceVectorMass d.potential (energyLimitFlux d V) x +
        sourceVectorJacobianEnergy (energyLimitJacobian d V) x) := by
    filter_upwards [energyLimitFlux_mass_square_ae d V, energyLimitJacobian_square_ae d V hZ] with x hm hq
    simpa only [Fintype.sum_sum_type, Fintype.sum_prod_type] using congrArg₂ (fun a b : ℝ => a + b) hm hq
  rw [← integral_congr_ae he]
  rw [integral_finsetSum Finset.univ (fun a _ => (Lp.memLp (V a)).integrable_sq), PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_congr rfl fun a _ => (L2.norm_sq_eq_integral_sq (V a)).symm

end KLSConstantImprovement.ActualSourceLimitGaffneyEnergy405
#print axioms KLSConstantImprovement.ActualSourceLimitGaffneyEnergy405.energyLimitJacobianMatrix_eq_root_sandwich
#print axioms KLSConstantImprovement.ActualSourceLimitGaffneyEnergy405.energyLimitJacobian_compatible_ae
#print axioms KLSConstantImprovement.ActualSourceLimitGaffneyEnergy405.energyLimitFlux_mass_square_ae
#print axioms KLSConstantImprovement.ActualSourceLimitGaffneyEnergy405.energyLimitJacobian_square_ae
#print axioms KLSConstantImprovement.ActualSourceLimitGaffneyEnergy405.energyLimitGaffney_integrable
#print axioms KLSConstantImprovement.ActualSourceLimitGaffneyEnergy405.energyLimitGaffney_integral_eq_norm_sq

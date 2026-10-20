import KLSConstantImprovement.ActualSourceLimitFluxDomains405
import KLSConstantImprovement.ActualMaximalRawMetricDomain405

/-! Exact actual-metric relations of the common energy limit.  The raw
scalar gradient has finite canonical energy, paid by its literal L2 mass
block, and its inverse-Hessian flux is the constructed limit flux. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceLimitMetricRelations405
open KLS ActualBoundedCanonicalSource ActualSourceRegularizedEnergyVector405
open ActualSourceLimitFluxDomains405 ActualCompactRawMetricGraph ActualMaximalRawMetricDomain405
open ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricCore ActualWeakCanonicalMetricOrdinaryGraph
open ActualSourceMetricFaithfulness405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem energyLimitScalarGradient_raw_metric_ae (d : SourceData μ) (V : GaffneyEnergyAmbient d) (i : Fin n) :
    rawCanonicalMetricDerivative d.potential (energyLimitScalarGradient d V) i
      =ᵐ[potentialMeasure d.potential] (V (Sum.inl i) : Space n → ℝ) := by
  filter_upwards [d.hessian_ae_source] with x hx
  change (canonicalMetricRoot d.potential x *ᵥ
    (canonicalMetricUnroot d.potential x *ᵥ (fun a => V (Sum.inl a) x))) i = V (Sum.inl i) x
  rw [Matrix.mulVec_mulVec, canonicalMetricRoot_mul_unroot_at hx.1, Matrix.one_mulVec]

theorem energyLimitFlux_eq_inverseGradient_ae (d : SourceData μ) (V : GaffneyEnergyAmbient d) (i : Fin n) :
    (fun x => ∑ a : Fin n, (coordinateHessian d.potential x)⁻¹ i a * energyLimitScalarGradient d V a x)
      =ᵐ[potentialMeasure d.potential] energyLimitFlux d V i := by
  filter_upwards [d.hessian_ae_source] with x hx
  have hJ : (coordinateHessian d.potential x)⁻¹ =
      canonicalMetricRoot d.potential x * canonicalMetricRoot d.potential x := by
    have he := canonicalMetricRoot_gram_at hx.1
    unfold canonicalMetricRoot at he
    rw [(inverseSqrtMatrix_isSymm (coordinateHessian d.potential x)).eq] at he
    exact he.symm
  change ((coordinateHessian d.potential x)⁻¹ *ᵥ
    (canonicalMetricUnroot d.potential x *ᵥ (fun a => V (Sum.inl a) x))) i =
      (canonicalMetricRoot d.potential x *ᵥ (fun a => V (Sum.inl a) x)) i
  rw [Matrix.mulVec_mulVec, hJ, Matrix.mul_assoc,
    canonicalMetricRoot_mul_unroot_at hx.1, Matrix.mul_one]

theorem energyLimitScalarGradient_energy_ae (d : SourceData μ) (V : GaffneyEnergyAmbient d) :
    (fun x => ∑ i : Fin n, V (Sum.inl i) x ^ 2) =ᵐ[potentialMeasure d.potential]
      rawInverseHessianGradientForm d.potential (energyLimitScalarGradient d V) := by
  filter_upwards [d.raw_metric_derivative_sq_ae (energyLimitScalarGradient d V),
    ae_all_iff.mpr (energyLimitScalarGradient_raw_metric_ae d V)] with x hx hv
  rw [← hx]
  exact Finset.sum_congr rfl fun i _ => congrArg (fun t : ℝ => t ^ 2) (hv i).symm

theorem energyLimitScalarGradient_energy_integrable (d : SourceData μ) (V : GaffneyEnergyAmbient d) :
    Integrable (rawInverseHessianGradientForm d.potential (energyLimitScalarGradient d V))
      (potentialMeasure d.potential) := by
  have hi : Integrable (fun x => ∑ i : Fin n, V (Sum.inl i) x ^ 2) (potentialMeasure d.potential) :=
    integrable_finsetSum Finset.univ (fun i _ => (Lp.memLp (V (Sum.inl i))).integrable_sq)
  exact hi.congr (energyLimitScalarGradient_energy_ae d V)

theorem energyLimitScalarGradient_energy_le_norm_sq (d : SourceData μ) (V : GaffneyEnergyAmbient d) :
    (∫ x, rawInverseHessianGradientForm d.potential (energyLimitScalarGradient d V) x
      ∂potentialMeasure d.potential) ≤ ‖V‖ ^ 2 := by
  have he : (∫ x, rawInverseHessianGradientForm d.potential (energyLimitScalarGradient d V) x
      ∂potentialMeasure d.potential) = ∑ i : Fin n, ‖V (Sum.inl i)‖ ^ 2 := by
    rw [← integral_congr_ae (energyLimitScalarGradient_energy_ae d V)]
    rw [integral_finsetSum Finset.univ (fun i _ => (Lp.memLp (V (Sum.inl i))).integrable_sq)]
    exact Finset.sum_congr rfl fun i _ => (L2.norm_sq_eq_integral_sq (V (Sum.inl i))).symm
  have hn := PiLp.norm_sq_eq_of_L2 (fun _ : GaffneyEnergyIndex n => Lp ℝ 2 (potentialMeasure d.potential)) V
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type] at hn
  rw [he, hn]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg ‖V (Sum.inr (i, j))‖)

end KLSConstantImprovement.ActualSourceLimitMetricRelations405
#print axioms KLSConstantImprovement.ActualSourceLimitMetricRelations405.energyLimitScalarGradient_raw_metric_ae
#print axioms KLSConstantImprovement.ActualSourceLimitMetricRelations405.energyLimitFlux_eq_inverseGradient_ae
#print axioms KLSConstantImprovement.ActualSourceLimitMetricRelations405.energyLimitScalarGradient_energy_ae
#print axioms KLSConstantImprovement.ActualSourceLimitMetricRelations405.energyLimitScalarGradient_energy_integrable
#print axioms KLSConstantImprovement.ActualSourceLimitMetricRelations405.energyLimitScalarGradient_energy_le_norm_sq

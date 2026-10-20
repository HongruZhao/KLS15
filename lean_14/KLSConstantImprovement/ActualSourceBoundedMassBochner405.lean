import KLSConstantImprovement.ActualSourceBoundedMassConnectionLimit405
import KLSConstantImprovement.ActualSourceNaturalHessian405

/-! Constant-one natural canonical Bochner completion under an explicit
bounded natural mass. The Hessian is a proved genuine weak derivative of
the constructed inverse gradient. Every global connection domain and
boundary limit is derived before the exact balance is integrated. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff NNReal ENNReal
namespace KLSConstantImprovement.ActualSourceBoundedMassBochner405
open KLS ActualBoundedCanonicalSource ActualSourceConnectionFields405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
open ActualSourceNaturalTargetCurvatureDomain405 ActualSourceConnectionPointwise405
open ActualSourceBoundedMassGammaDomain405 ActualSourceBoundedMassConnectionLimit405 ActualSourceNaturalHessian405
open ActualCompatibleConnectionYoung405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem naturalCanonicalHessianEnergy_nonnegative_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hc : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i j => Du i j x)).IsSymm) :
    ∀ᵐ x ∂potentialMeasure d.potential, 0 ≤ naturalCanonicalHessianEnergy d g Du x := by
  filter_upwards [d.hessian_ae_source, naturalCanonicalHessian_isSymm_ae d g Du hc] with x hp hC
  have he := whitened_connection_square (coordinateHessian d.potential x)
    (naturalCanonicalHessian d g Du x) hp.1 hC
  unfold naturalCanonicalHessianEnergy
  rw [← he]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

theorem actual_natural_bochner_identity_of_mass_bound (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d g) x ≤ C)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i j E, IsCompact E → MemLp (Du i j) 2 (volume.restrict E))
    (hw : ∀ i j, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i j) j)
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i j => Du i j x)).IsSymm)
    (hMi : Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g)) (potentialMeasure d.potential))
    (hQi : Integrable (sourceVectorJacobianEnergy Du) (potentialMeasure d.potential)) :
    Integrable (naturalCanonicalHessianEnergy d g Du) (potentialMeasure d.potential) ∧
      (∫ x, naturalCanonicalHessianEnergy d g Du x + sourceConnectionTarget d (naturalCanonicalFlux d g) x
        ∂potentialMeasure d.potential) =
      ∫ x, sourceVectorMass d.potential (naturalCanonicalFlux d g) x + sourceVectorJacobianEnergy Du x
        ∂potentialMeasure d.potential := by
  let u := naturalCanonicalFlux d g
  let ν := potentialMeasure d.potential
  change Integrable (sourceVectorMass d.potential u) ν at hMi
  change Integrable (sourceVectorJacobianEnergy Du) ν at hQi
  have hG : Integrable (sourceConnectionGamma d u) ν :=
    (actual_Gamma_integrable_of_bounded_natural_mass d g hC hM Du hu hDu hw hcomp hMi hQi).1
  have hP : Integrable (sourceConnectionTarget d u) ν := natural_targetCurvature_integrable d g
  have hX : Integrable (sourceConnectionCross d u Du) ν :=
    actual_connectionCross_integrable_of_mass_bound d g hC hM Du hu hDu hw hcomp hMi hQi
  have hQX : Integrable (fun x => sourceVectorJacobianEnergy Du x + sourceConnectionCross d u Du x) ν := hQi.add hX
  have hQXG : Integrable (fun x => sourceVectorJacobianEnergy Du x + sourceConnectionCross d u Du x +
      sourceConnectionGamma d u x) ν := hQX.add hG
  have hE : Integrable (naturalCanonicalHessianEnergy d g Du) ν :=
    hQXG.congr (naturalCanonicalHessianEnergy_eq_ae d g Du).symm
  have hEI : (∫ x, naturalCanonicalHessianEnergy d g Du x ∂ν) =
      (∫ x, sourceVectorJacobianEnergy Du x ∂ν) +
      (∫ x, sourceConnectionCross d u Du x ∂ν) + (∫ x, sourceConnectionGamma d u x ∂ν) := by
    calc
      _ = ∫ x, sourceVectorJacobianEnergy Du x + sourceConnectionCross d u Du x +
          sourceConnectionGamma d u x ∂ν := integral_congr_ae (naturalCanonicalHessianEnergy_eq_ae d g Du)
      _ = _ := by rw [integral_add hQX hG, integral_add hQi hX]
  have hbalance : (∫ x, sourceConnectionTarget d u x + sourceConnectionGamma d u x ∂ν) =
      (∫ x, sourceVectorMass d.potential u x ∂ν) - (∫ x, sourceConnectionCross d u Du x ∂ν) :=
    integral_actual_global_connection_balance_of_mass_bound d g hC hM Du hu hDu hw hcomp hMi hQi
  rw [integral_add hP hG] at hbalance
  refine ⟨hE, ?_⟩
  change (∫ x, naturalCanonicalHessianEnergy d g Du x + sourceConnectionTarget d u x ∂ν) =
    ∫ x, sourceVectorMass d.potential u x + sourceVectorJacobianEnergy Du x ∂ν
  rw [integral_add hE hP, integral_add hMi hQi, hEI]
  linarith

/-- The actual inverse supplies Du and every local/global domain. Only
bounded natural mass is extra; no Hessian, PDE or Bochner witness is an
input. This premise must be proved for the quadratic eta rows before
using the theorem as an original-law production estimate. -/
theorem exists_naturalCanonicalHessian_bochner_of_mass_bound (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d g) x ≤ C) :
    ∃ Du : Fin n → Fin n → Space n → ℝ,
      (∀ i j E, IsCompact E → MemLp (Du i j) 2 (volume.restrict E)) ∧
      (∀ i j, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i j) j) ∧
      (∀ᵐ x ∂(volume : Measure (Space n)),
        (coordinateHessian d.potential x * Matrix.of (fun i j => Du i j x)).IsSymm) ∧
      (∀ i j E, IsCompact E → MemLp (fun x => naturalCanonicalHessian d g Du x i j) 2 (volume.restrict E)) ∧
      (∀ i j, HasLocalWeakCoordinateDerivative (naturalCanonicalRawGradient d g i)
        (fun x => naturalCanonicalHessian d g Du x i j) j) ∧
      (∀ᵐ x ∂potentialMeasure d.potential, (naturalCanonicalHessian d g Du x).IsSymm) ∧
      Integrable (naturalCanonicalHessianEnergy d g Du) (potentialMeasure d.potential) ∧
      Integrable (sourceConnectionGamma d (naturalCanonicalFlux d g)) (potentialMeasure d.potential) ∧
      Integrable (sourceConnectionTarget d (naturalCanonicalFlux d g)) (potentialMeasure d.potential) ∧
      (∫ x, naturalCanonicalHessianEnergy d g Du x + sourceConnectionTarget d (naturalCanonicalFlux d g) x
        ∂potentialMeasure d.potential) ≤ ‖g‖ ^ 2 := by
  obtain ⟨Du, hu, hDu, hw, hcomp, hMi, hQi, hbound, _⟩ := exists_naturalCanonicalFlux_gaffney d hn g hg
  obtain ⟨hE, hEI⟩ := actual_natural_bochner_identity_of_mass_bound d g hC hM Du hu hDu hw hcomp hMi hQi
  refine ⟨Du, hDu, hw, hcomp, ?_, ?_, naturalCanonicalHessian_isSymm_ae d g Du hcomp,
    hE, ?_, natural_targetCurvature_integrable d g, ?_⟩
  · exact naturalCanonicalHessian_local_L2 d g hC hM Du hDu
  · exact naturalCanonicalRawGradient_hasLocalWeakDerivative d g hC hM Du hu hDu hw
  · exact (actual_Gamma_integrable_of_bounded_natural_mass d g hC hM Du hu hDu hw hcomp hMi hQi).1
  · rw [hEI]
    exact hbound

end KLSConstantImprovement.ActualSourceBoundedMassBochner405
#print axioms KLSConstantImprovement.ActualSourceBoundedMassBochner405.naturalCanonicalHessianEnergy_nonnegative_ae
#print axioms KLSConstantImprovement.ActualSourceBoundedMassBochner405.actual_natural_bochner_identity_of_mass_bound
#print axioms KLSConstantImprovement.ActualSourceBoundedMassBochner405.exists_naturalCanonicalHessian_bochner_of_mass_bound

import KLSConstantImprovement.ActualSourceNaturalWhitenedHessian405
import KLSConstantImprovement.ActualMaximalRawMetricDomain405

/-! Genuine natural scalar-form membership of the ordinary inverse
coordinate gradient, derived from its actual whitened Hessian L2 domain.
The bounded-mass gate is explicit only in the final constructed wrapper. -/
noncomputable section
open MeasureTheory Matrix Set Filter
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualNaturalGradientForm405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualSourceNaturalWhitenedHessian405 ActualSourceNaturalHessian405
open ActualSourceNaturalTargetCurvatureDomain405 ActualSourceNaturalGaffney405
open ActualSourceLimitFluxDomains405 ActualWeakCanonicalMetricOrdinaryGraph
open ActualSourceMetricFaithfulness405 ActualMaximalRawMetricDomain405 ActualCompactRawMetricGraph
open ActualSourceLocalizedGaffney405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem natural_rawGradient_metric_derivative_memLp (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (Du : Fin n → Fin n → Space n → ℝ)
    (hW : ∀ a b, MemLp (fun x => naturalWhitenedHessian d g Du x a b) 2 (potentialMeasure d.potential))
    (i r : Fin n) :
    MemLp (rawCanonicalMetricDerivative d.potential (fun a x => naturalCanonicalHessian d g Du x i a) r)
      2 (potentialMeasure d.potential) := by
  have hS (a b : Fin n) := actualUnroot_entry_memLp_top d a b
  have hm : MemLp (fun x => (canonicalMetricUnroot d.potential x * naturalWhitenedHessian d g Du x) i r)
      2 (potentialMeasure d.potential) :=
    memLp_matrix_mul_entries (p := ∞) (q := 2) (r := 2) hS hW i r
  apply (memLp_congr_ae ?_).mp hm
  filter_upwards [d.hessian_ae_source, naturalCanonicalHessian_reconstruct_ae d g Du] with x hx hC
  let S := canonicalMetricUnroot d.potential x
  let R := canonicalMetricRoot d.potential x
  let C := naturalCanonicalHessian d g Du x
  let W := naturalWhitenedHessian d g Du x
  have hSR : S * R = 1 := canonicalMetricUnroot_mul_root_at hx.1
  have hCR : C * R = S * W := by
    change C = S * W * S at hC
    rw [hC, Matrix.mul_assoc, hSR, Matrix.mul_one]
  change (S * W) i r = _
  rw [← hCR]
  simp only [Matrix.mul_apply, rawCanonicalMetricDerivative]
  apply Finset.sum_congr rfl
  intro a _
  have hR : R.IsSymm := inverseSqrtMatrix_isSymm _
  change C i a * R a r = R r a * C i a
  rw [hR.apply r a]
  ring

theorem exists_natural_gradient_coordinate_form (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (Du : Fin n → Fin n → Space n → ℝ)
    (hW : ∀ a b, MemLp (fun x => naturalWhitenedHessian d g Du x a b) 2 (potentialMeasure d.potential))
    (hC : ∀ a b, MemLp (fun x => naturalCanonicalHessian d g Du x a b) 2 (potentialMeasure d.potential))
    (hw : ∀ i j, HasLocalWeakCoordinateDerivative (naturalCanonicalRawGradient d g i)
      (fun x => naturalCanonicalHessian d g Du x i j) j) (i : Fin n) :
    ∃ U : CanonicalMetricH1 d.potential,
      (canonicalMetricValue d.potential U : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
        (fun x => naturalCanonicalRawGradient d g i x -
          ∫ y, naturalCanonicalRawGradient d g i y ∂potentialMeasure d.potential) ∧
      ∀ r, (canonicalMetricGradient d.potential r U : Space n → ℝ)
        =ᵐ[potentialMeasure d.potential]
          rawCanonicalMetricDerivative d.potential (fun a x => naturalCanonicalHessian d g Du x i a) r := by
  have hi (r : Fin n) := natural_rawGradient_metric_derivative_memLp d g Du hW i r
  have he : Integrable (rawInverseHessianGradientForm d.potential
      (fun a x => naturalCanonicalHessian d g Du x i a)) (potentialMeasure d.potential) :=
    (integrable_finsetSum Finset.univ (fun r _ => (hi r).integrable_sq)).congr
      (d.raw_metric_derivative_sq_ae (fun a x => naturalCanonicalHessian d g Du x i a))
  exact d.maximal_raw_metric_pair_mem (naturalCanonicalRawGradient_memLp d g i)
    (fun a E hE => KLS.MemLp.restrict_volume_of_potentialMeasure (hC i a) d.source_C1.continuous hE)
    (hw i) he

theorem exists_natural_gradient_forms_of_mass_bound (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d g) x ≤ C) :
    ∃ Du : Fin n → Fin n → Space n → ℝ,
      (∀ a b, MemLp (fun x => naturalWhitenedHessian d g Du x a b) 2 (potentialMeasure d.potential)) ∧
      (∀ a b, MemLp (fun x => naturalCanonicalHessian d g Du x a b) 2 (potentialMeasure d.potential)) ∧
      (∫ x, matrixFrobeniusSq (naturalWhitenedHessian d g Du x) ∂potentialMeasure d.potential) ≤ ‖g‖ ^ 2 ∧
      ∃ U : Fin n → CanonicalMetricH1 d.potential,
        (∀ i, (canonicalMetricValue d.potential (U i) : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
          (fun x => naturalCanonicalRawGradient d g i x -
            ∫ y, naturalCanonicalRawGradient d g i y ∂potentialMeasure d.potential)) ∧
        ∀ i r, (canonicalMetricGradient d.potential r (U i) : Space n → ℝ)
          =ᵐ[potentialMeasure d.potential]
            rawCanonicalMetricDerivative d.potential (fun a x => naturalCanonicalHessian d g Du x i a) r := by
  obtain ⟨Du, hW, hCl2, hw, hb⟩ := exists_naturalHessian_global_L2_of_mass_bound d hn g hg hC hM
  choose U hU using fun i => exists_natural_gradient_coordinate_form d g Du hW hCl2 hw i
  exact ⟨Du, hW, hCl2, hb, U, fun i => (hU i).1, fun i r => (hU i).2 r⟩

end KLSConstantImprovement.ActualNaturalGradientForm405
#print axioms KLSConstantImprovement.ActualNaturalGradientForm405.natural_rawGradient_metric_derivative_memLp
#print axioms KLSConstantImprovement.ActualNaturalGradientForm405.exists_natural_gradient_coordinate_form
#print axioms KLSConstantImprovement.ActualNaturalGradientForm405.exists_natural_gradient_forms_of_mass_bound

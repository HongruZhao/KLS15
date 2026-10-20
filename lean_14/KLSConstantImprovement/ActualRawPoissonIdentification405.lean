import KLSConstantImprovement.ActualMaximalRawMetricDomain405
import KLSConstantImprovement.ActualSourceRawMetricPair405
import KLSConstantImprovement.ActualSourceFormCompanions405
import KLS.WeightedResolventWeakEquation

/-!
Natural weak Poisson solutions with their actual raw finite energy are
identified with the constructed canonical inverse. Compact form density
is used only to pass a continuous first-order variational equation.
There is no compact strong operator core or range-density assertion.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter InnerProductSpace
open scoped BigOperators ContDiff Topology ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualRawPoissonIdentification405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualCompactRawMetricGraph ActualMaximalRawMetricDomain405 ActualSourceRawMetricPair405
open ActualSourceFormCompanions405 ActualWeakCanonicalMetricInverse
variable {n : ℕ} {μ : Measure (Space n)}

/-- Literal raw inverse-Hessian weak pairing of a finite-energy form
representative with a compact scalar test. All form coordinates are the
actual weak ones supplied by maximal raw-domain membership. -/
theorem canonicalMetricEnergy_eq_raw_test_pair (d : SourceData μ)
    (U V : CanonicalMetricH1 d.potential) (F : Fin n → Space n → ℝ)
    (ψ : Space n → ℝ)
    (hU : ∀ i, (canonicalMetricGradient d.potential i U : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential] rawCanonicalMetricDerivative d.potential F i)
    (hV : ∀ i, (canonicalMetricGradient d.potential i V : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential] canonicalMetricDerivative d.potential ψ i) :
    canonicalMetricEnergy d.potential U V =
      ∫ x, ∑ a, ∑ b, (coordinateHessian d.potential x)⁻¹ a b * F a x *
        coordinateDerivative ψ b x ∂potentialMeasure d.potential := by
  have hi (i : Fin n) : Integrable (fun x => canonicalMetricGradient d.potential i U x *
      canonicalMetricGradient d.potential i V x) (potentialMeasure d.potential) :=
    (Lp.memLp (canonicalMetricGradient d.potential i U)).integrable_mul
      (Lp.memLp (canonicalMetricGradient d.potential i V))
  rw [canonicalMetricEnergy_apply]
  simp_rw [L2.real_inner_eq_integral]
  rw [← integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr hU, ae_all_iff.mpr hV,
    actual_raw_metric_pair_ae d F (fun j x => coordinateDerivative ψ j x)] with x hx hy hp
  calc
    _ = ∑ i, rawCanonicalMetricDerivative d.potential F i x *
        rawCanonicalMetricDerivative d.potential (fun j y => coordinateDerivative ψ j y) i x := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hx i, hy i]
      rfl
    _ = _ := hp

/-- Compact scalar tests already determine the full natural variational
solution because they are a form core. No second-order domain is used. -/
theorem canonicalMetricInverse_eq_of_compact_form_equation (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (U : CanonicalMetricH1 d.potential)
    (hEq : ∀ (ψ : Space n → ℝ), ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      ∀ V : CanonicalMetricH1 d.potential,
        (canonicalMetricValue d.potential V : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
          (fun x => ψ x - ∫ y, ψ y ∂potentialMeasure d.potential) →
        (∀ i, (canonicalMetricGradient d.potential i V : Space n → ℝ)
          =ᵐ[potentialMeasure d.potential] canonicalMetricDerivative d.potential ψ i) →
        canonicalMetricEnergy d.potential U V = inner ℝ g (canonicalMetricValue d.potential V)) :
    U = sourceMetricInverseH1 d g := by
  apply sourceMetricInverse_unique d g
  intro V
  obtain ⟨ψ, W, hW, hlim⟩ := exists_actual_compact_form_approximation d V
  have he (k : ℕ) : canonicalMetricEnergy d.potential U (W k) =
      inner ℝ g (canonicalMetricValue d.potential (W k)) :=
    hEq (ψ k) (hW k).1 (hW k).2.1 (W k) (hW k).2.2.1 (hW k).2.2.2
  have hl := (canonicalMetricEnergy d.potential U).continuous.continuousAt.tendsto.comp hlim
  have hr : Tendsto (fun k => inner ℝ g (canonicalMetricValue d.potential (W k)))
      atTop (𝓝 (inner ℝ g (canonicalMetricValue d.potential V))) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => g) atTop (𝓝 g)).inner
      ((canonicalMetricValue d.potential).continuous.continuousAt.tendsto.comp hlim)
  exact tendsto_nhds_unique hl (hr.congr fun k => (he k).symm)

/-- An actual raw weak source solution is the actual canonical inverse.
The only equation supplied is the literal compact distribution equation;
all form membership and the natural inverse identification are proved. -/
theorem exists_actual_inverse_of_raw_compact_equation (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0)
    {f : Space n → ℝ} {F : Fin n → Space n → ℝ}
    (hf : MemLp f 2 (potentialMeasure d.potential))
    (hFloc : ∀ j E, IsCompact E → MemLp (F j) 2 (volume.restrict E))
    (hFw : ∀ j, HasLocalWeakCoordinateDerivative f (F j) j)
    (henergy : Integrable (rawInverseHessianGradientForm d.potential F)
      (potentialMeasure d.potential))
    (hEq : ∀ (ψ : Space n → ℝ), ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∫ x, ∑ a, ∑ b, (coordinateHessian d.potential x)⁻¹ a b * F a x *
        coordinateDerivative ψ b x ∂potentialMeasure d.potential) =
        ∫ x, g x * ψ x ∂potentialMeasure d.potential) :
    (sourceMetricInverse d g : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
      (fun x => f x - ∫ y, f y ∂potentialMeasure d.potential) ∧
    ∀ i, (canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g) : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential] rawCanonicalMetricDerivative d.potential F i := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  obtain ⟨U, hu, hd⟩ := d.maximal_raw_metric_pair_mem hf hFloc hFw henergy
  have he : U = sourceMetricInverseH1 d g := by
    apply canonicalMetricInverse_eq_of_compact_form_equation d g U
    intro ψ hψ hc V hv hV
    rw [canonicalMetricEnergy_eq_raw_test_pair d U V F ψ hd hV, hEq ψ hψ hc]
    have hψ2 := memLp_of_continuous_hasCompactSupport d.source_C1.continuous hψ.continuous hc
    rw [weighted_inner_centered_test hψ2 hv, hg, zero_mul, sub_zero]
  rw [he] at hu hd
  exact ⟨hu, hd⟩

end KLSConstantImprovement.ActualRawPoissonIdentification405

#print axioms KLSConstantImprovement.ActualRawPoissonIdentification405.canonicalMetricEnergy_eq_raw_test_pair
#print axioms KLSConstantImprovement.ActualRawPoissonIdentification405.canonicalMetricInverse_eq_of_compact_form_equation
#print axioms KLSConstantImprovement.ActualRawPoissonIdentification405.exists_actual_inverse_of_raw_compact_equation

import KLSConstantImprovement.ActualSourceCanonicalConnectionBalance405
import KLSConstantImprovement.ActualSourceCanonicalConnectionTest405
import KLSConstantImprovement.ActualSourceCompactCanonicalBochner405

/-!
Positive compact canonical Bochner on the actual C1,1 source. The signed
Jacobian formula and the connection product test have genuine weak raw H1
domains. All integrability needed to combine them is paid here on compact
sets; no compact strong-operator core is asserted.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceCompactPositiveBochner405
open KLS ActualBoundedCanonicalSource ActualSourceInverseTensor405
open ActualSourceInverseGradientDomain405 ActualSourceCanonicalConnectionTest405
open ActualSourceCanonicalConnectionBalance405 ActualSourceCompactCanonicalBochner405
open ActualSourceCompactOperator405
variable {n : ℕ} {μ : Measure (Space n)}

private theorem source_integrable_of_compact_local (d : SourceData μ)
    {f : Space n → ℝ} (hc : HasCompactSupport f)
    (hf : ∀ E, IsCompact E → Integrable f (volume.restrict E)) :
    Integrable f (potentialMeasure d.potential) := by
  rw [integrable_potentialMeasure_iff d.source_C1.continuous.measurable]
  have hρ : Continuous (fun x => Real.exp (-d.potential x)) :=
    Real.continuous_exp.comp d.source_C1.continuous.neg
  have hi := IntegrableOn.continuousOn_mul hρ.continuousOn (hf _ hc) hc
  have hs : Function.support (fun x => f x * Real.exp (-d.potential x)) ⊆ tsupport f :=
    (subset_tsupport _).trans tsupport_mul_subset_left
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  simpa only [mul_comm] using hi

private theorem connection_left_term_integrable (d : SourceData μ)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) (k i a : Fin n) :
    Integrable (fun x => actualInverseTensor d k x a i *
      (actualInverseGradientDerivative d ψ k a x * coordinateDerivative ψ i x +
        actualInverseGradient d ψ k x * coordinateHessian ψ x a i))
      (potentialMeasure d.potential) := by
  have hs : HasCompactSupport (fun x => actualInverseTensor d k x a i *
      (actualInverseGradientDerivative d ψ k a x * coordinateDerivative ψ i x +
        actualInverseGradient d ψ k x * coordinateHessian ψ x a i)) :=
    (((inverseGradientDerivative_compact d hc k a).mul_right).add
      ((inverseGradient_compact d hc k).mul_right)).mul_left
  apply source_integrable_of_compact_local d hs
  intro E hE
  have hp := memLp_top_restrict_compact_of_continuous
    (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous hE
  have hC : MemLp (fun x => coordinateHessian ψ x a i) 2 (volume.restrict E) :=
    memLp_continuous_on_compact
    (contDiff_coordinateHessian hψ (m := 0) (by norm_num) a i).continuous hE
  have hfirst : MemLp (fun x => actualInverseGradientDerivative d ψ k a x *
      coordinateDerivative ψ i x) 2 (volume.restrict E) := by
    have hm : MemLp (fun x => coordinateDerivative ψ i x *
        actualInverseGradientDerivative d ψ k a x) 2 (volume.restrict E) :=
      hp.mul (inverseGradientDerivative_local_L2 d hψ k a E hE)
    exact (memLp_congr_ae (Eventually.of_forall fun x => mul_comm _ _)).mp hm
  have hF : MemLp (fun x => actualInverseGradientDerivative d ψ k a x *
      coordinateDerivative ψ i x + actualInverseGradient d ψ k x * coordinateHessian ψ x a i)
      2 (volume.restrict E) :=
    hfirst.add ((inverseGradient_local_top d (hψ.of_le (by norm_num)) k E hE).mul hC)
  exact (inverse_tensor_local_L2 d k a i E hE).integrable_mul hF

private theorem connection_right_term_integrable (d : SourceData μ)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) (k i : Fin n) :
    Integrable (fun x => ((1 : Matrix (Fin n) (Fin n) ℝ) k i -
      (coordinateHessian d.potential x * coordinateHessian d.targetPotential
        (gradient d.potential x)) k i) *
      (actualInverseGradient d ψ k x * coordinateDerivative ψ i x))
      (potentialMeasure d.potential) := by
  have hs : HasCompactSupport (fun x => ((1 : Matrix (Fin n) (Fin n) ℝ) k i -
      (coordinateHessian d.potential x * coordinateHessian d.targetPotential
        (gradient d.potential x)) k i) *
      (actualInverseGradient d ψ k x * coordinateDerivative ψ i x)) :=
    ((inverseGradient_compact d hc k).mul_right).mul_left
  apply source_integrable_of_compact_local d hs
  intro E hE
  letI : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hE.measure_ne_top
  have hHP : MemLp (fun x => (coordinateHessian d.potential x *
      coordinateHessian d.targetPotential (gradient d.potential x)) k i) ∞ (volume.restrict E) := by
    simp only [Matrix.mul_apply]
    exact memLp_finsetSum Finset.univ fun b _ =>
      (memLp_top_actual_hessian_of_locallyLipschitz_gradient d.gradient_lipschitz.locallyLipschitz
        k b hE).mul (memLp_top_restrict_compact_of_continuous
          ((contDiff_coordinateHessian (d.target_smooth.of_le (by simp) :
              ContDiff ℝ 2 d.targetPotential) (m := 0) (by norm_num) b i).continuous.comp
            d.gradient_lipschitz.continuous) hE)
  have hconst : MemLp (fun _ : Space n => (1 : Matrix (Fin n) (Fin n) ℝ) k i)
      ∞ (volume.restrict E) := memLp_const _
  have hu2 := (inverseGradient_local_top d (hψ.of_le (by norm_num)) k E hE).mono_exponent
    (by norm_num : (2 : ℝ≥0∞) ≤ (⊤ : ENNReal))
  have hp := memLp_top_restrict_compact_of_continuous
    (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous hE
  have hup : MemLp (fun x => actualInverseGradient d ψ k x * coordinateDerivative ψ i x)
      2 (volume.restrict E) := by
    have hm : MemLp (fun x => coordinateDerivative ψ i x * actualInverseGradient d ψ k x)
        2 (volume.restrict E) := hp.mul hu2
    exact (memLp_congr_ae (Eventually.of_forall fun x => mul_comm _ _)).mp hm
  have hprod : MemLp (fun x => ((1 : Matrix (Fin n) (Fin n) ℝ) k i -
      (coordinateHessian d.potential x * coordinateHessian d.targetPotential
        (gradient d.potential x)) k i) *
      (actualInverseGradient d ψ k x * coordinateDerivative ψ i x)) 2 (volume.restrict E) :=
    (hconst.sub hHP).mul hup
  exact hprod.integrable (by norm_num)

private theorem prebochner_integrable (d : SourceData μ)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) :
    Integrable (actualCanonicalPrebochnerDensity d ψ) (potentialMeasure d.potential) := by
  unfold actualCanonicalPrebochnerDensity
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  have hs : HasCompactSupport (fun x =>
      coordinateHessian d.potential x i j * actualInverseGradient d ψ i x *
        actualInverseGradient d ψ j x + actualInverseGradientDerivative d ψ i j x *
          actualInverseGradientDerivative d ψ j i x) :=
    (((inverseGradient_compact d hc i).mul_left).mul_right).add
      ((inverseGradientDerivative_compact d hc i j).mul_right)
  apply source_integrable_of_compact_local d hs
  intro E hE
  letI : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hE.measure_ne_top
  have hui : MemLp (actualInverseGradient d ψ i) 2 (volume.restrict E) :=
    (inverseGradient_local_top d (hψ.of_le (by norm_num)) i E hE).mono_exponent (by norm_num)
  have huj : MemLp (actualInverseGradient d ψ j) 2 (volume.restrict E) :=
    (inverseGradient_local_top d (hψ.of_le (by norm_num)) j E hE).mono_exponent (by norm_num)
  have hH := memLp_top_actual_hessian_of_locallyLipschitz_gradient
    d.gradient_lipschitz.locallyLipschitz i j hE
  have hHi : MemLp (fun x => coordinateHessian d.potential x i j * actualInverseGradient d ψ i x)
      2 (volume.restrict E) := hH.mul hui
  exact (hHi.integrable_mul huj).add
    ((inverseGradientDerivative_local_L2 d hψ i j E hE).integrable_mul
      (inverseGradientDerivative_local_L2 d hψ j i E hE))

/-- Every term of the actual connection product test is integrable, so
the finite sum can be combined before taking its source integral. -/
theorem compact_actual_connection_integral (d : SourceData μ)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) :
    (∫ x, actualConnectionLeftDensity d ψ x ∂potentialMeasure d.potential) =
      ∫ x, actualConnectionRightDensity d ψ x ∂potentialMeasure d.potential := by
  have hL := connection_left_term_integrable d hψ hc
  have hR := connection_right_term_integrable d hψ hc
  unfold actualConnectionLeftDensity actualConnectionRightDensity
  rw [integral_finsetSum Finset.univ (fun k _ => integrable_finsetSum Finset.univ
      (fun i _ => integrable_finsetSum Finset.univ (fun a _ => hL k i a))),
    integral_finsetSum Finset.univ (fun k _ => integrable_finsetSum Finset.univ (fun i _ => hR k i))]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun a _ => hL k i a)),
    integral_finsetSum Finset.univ (fun i _ => hR k i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun a _ => hL k i a)]
  exact actual_compact_connection_product_test d hψ hc k i

/-- Exact positive canonical Bochner on the actual C1,1 source. This is
a compact scalar theorem; natural resolvent-domain extension is separate. -/
theorem compact_actual_positive_canonical_bochner (d : SourceData μ)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    Integrable (actualCanonicalPositiveDensity d ψ) (potentialMeasure d.potential) ∧
      (∫ x, actualSourceOperator d ψ x ^ 2 ∂potentialMeasure d.potential) =
        ∫ x, actualCanonicalPositiveDensity d ψ x ∂potentialMeasure d.potential := by
  have hB := prebochner_integrable d (hψ.of_le (by norm_num)) hc
  have hL : Integrable (actualConnectionLeftDensity d ψ) (potentialMeasure d.potential) :=
    integrable_finsetSum Finset.univ fun k _ => integrable_finsetSum Finset.univ fun i _ =>
      integrable_finsetSum Finset.univ fun a _ =>
        connection_left_term_integrable d (hψ.of_le (by norm_num)) hc k i a
  have hR : Integrable (actualConnectionRightDensity d ψ) (potentialMeasure d.potential) :=
    integrable_finsetSum Finset.univ fun k _ => integrable_finsetSum Finset.univ fun i _ =>
      connection_right_term_integrable d (hψ.of_le (by norm_num)) hc k i
  have hbalance := actual_compact_connection_balance_ae d (hψ.of_le (by norm_num))
  have hP : Integrable (actualCanonicalPositiveDensity d ψ) (potentialMeasure d.potential) := by
    apply ((hB.add hL).sub hR).congr
    filter_upwards [hbalance] with x hx
    change actualCanonicalPrebochnerDensity d ψ x + actualConnectionLeftDensity d ψ x -
      actualConnectionRightDensity d ψ x = actualCanonicalPositiveDensity d ψ x
    linarith
  refine ⟨hP, ?_⟩
  have he := integral_congr_ae hbalance
  rw [integral_add hB hL, integral_add hP hR] at he
  have hconnection := compact_actual_connection_integral d (hψ.of_le (by norm_num)) hc
  have hb := compact_actual_canonical_prebochner d hψ hc
  change (∫ x, actualSourceOperator d ψ x ^ 2 ∂potentialMeasure d.potential) =
    ∫ x, actualCanonicalPrebochnerDensity d ψ x ∂potentialMeasure d.potential at hb
  linarith

end KLSConstantImprovement.ActualSourceCompactPositiveBochner405

#print axioms KLSConstantImprovement.ActualSourceCompactPositiveBochner405.compact_actual_connection_integral
#print axioms KLSConstantImprovement.ActualSourceCompactPositiveBochner405.compact_actual_positive_canonical_bochner

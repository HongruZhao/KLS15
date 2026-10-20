import KLSConstantImprovement.ActualSourceInverseGradientDomain405
import KLSConstantImprovement.ActualSourceCompactOperator405
import KLSConstantImprovement.ActualCompactWeakSourceVectorSquare
import KLS.WeakWeightedMean

/-!
Actual compact canonical pre-Bochner identity at C1,1 source regularity.
The source inverse gradient, its raw weak Jacobian, all compact/L2 domains
and its adjoint equal to the literal canonical generator are proved.
This retains the exact signed Jacobian trace. The remaining inverse-tensor
cancellation and natural noncompact domain passage are separate steps.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators ContDiff Topology ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceCompactCanonicalBochner405
open KLS ActualBoundedCanonicalSource ActualSourceInverseGradientDomain405 ActualSourceCompactOperator405
open ActualCompactWeakSourceVectorBochner ActualCompactWeakSourceVectorSquare
variable {n : ℕ} {μ : Measure (Space n)}

private theorem source_coordinate_top (d : SourceData μ) (i : Fin n) :
    MemLp (coordinateDerivative d.potential i) ∞ (potentialMeasure d.potential) :=
  source_coordinate_memLp_top_of_lipschitz d.source_lipschitz (potentialMeasure d.potential) i

theorem inverseGradient_adjoint_eq_operator_ae (d : SourceData μ)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    rawWeakSourceVectorAdjoint d.potential (actualInverseGradient d ψ)
      (actualInverseGradientDerivative d ψ) =ᵐ[potentialMeasure d.potential] actualSourceOperator d ψ := by
  letI := d.source_probability
  let u := actualInverseGradient d ψ
  let Du := actualInverseGradientDerivative d ψ
  let δu := rawWeakSourceVectorAdjoint d.potential u Du
  have hdom (i : Fin n) := inverseGradient_weighted_H1 d (hψ.of_le (by norm_num)) hc i
  have hδ (i : Fin n) : MemLp (rawWeakSourceAdjoint d.potential (u i) (Du i i) i)
      2 (potentialMeasure d.potential) :=
    ((source_coordinate_top d i).mul (hdom i).1).sub ((hdom i).2 i).1
  have hδu : MemLp δu 2 (potentialMeasure d.potential) :=
    memLp_finsetSum Finset.univ fun i _ => hδ i
  have hA := actualSourceOperator_memLp d (hψ.of_le (by norm_num)) hc
  have hpair {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) :
      (∫ x, δu x * χ x ∂potentialMeasure d.potential) =
        ∫ x, (∑ i : Fin n, u i x * coordinateDerivative χ i x) ∂potentialMeasure d.potential := by
    have hχ2 := memLp_of_continuous_hasCompactSupport d.source_C1.continuous hχ.continuous hχc
    have hDχ2 (i : Fin n) := memLp_of_continuous_hasCompactSupport d.source_C1.continuous
      (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) i).continuous
      (hasCompactSupport_coordinateDerivative hχc i)
    have hi (i : Fin n) : (∫ x, rawWeakSourceAdjoint d.potential (u i) (Du i i) i x * χ x
        ∂potentialMeasure d.potential) = ∫ x, u i x * coordinateDerivative χ i x
          ∂potentialMeasure d.potential := by
      have hfd : Integrable (fun x => u i x * coordinateDerivative d.potential i x)
          (potentialMeasure d.potential) := by
        have hm : MemLp (fun x => coordinateDerivative d.potential i x * u i x) 2
            (potentialMeasure d.potential) := (source_coordinate_top d i).mul (hdom i).1
        exact (hm.integrable (by norm_num)).congr (Eventually.of_forall fun x => mul_comm _ _)
      have hw := integral_raw_derivative_compact_weight d.source_C1 ((hdom i).2 i).2
        ((hdom i).1.integrable (by norm_num)) (((hdom i).2 i).1.integrable (by norm_num))
        hfd hχ hχc
      have hm2 : MemLp (fun x => coordinateDerivative d.potential i x * u i x) 2
          (potentialMeasure d.potential) := (source_coordinate_top d i).mul (hdom i).1
      have hfirst : Integrable (fun x => (u i x * coordinateDerivative d.potential i x) * χ x)
          (potentialMeasure d.potential) := by
        exact (hm2.integrable_mul hχ2).congr (Eventually.of_forall fun x => by
          simp only [Pi.mul_apply]
          ring)
      have hsecond : Integrable (fun x => Du i i x * χ x) (potentialMeasure d.potential) :=
        ((hdom i).2 i).1.integrable_mul hχ2
      have he : (∫ x, rawWeakSourceAdjoint d.potential (u i) (Du i i) i x * χ x
          ∂potentialMeasure d.potential) =
          (∫ x, (u i x * coordinateDerivative d.potential i x) * χ x ∂potentialMeasure d.potential) -
            ∫ x, Du i i x * χ x ∂potentialMeasure d.potential := by
        rw [← integral_sub hfirst hsecond]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by dsimp [rawWeakSourceAdjoint]; ring
      rw [he]
      linarith
    change (∫ x, (∑ i : Fin n, rawWeakSourceAdjoint d.potential (u i) (Du i i) i x) * χ x
      ∂potentialMeasure d.potential) = _
    simp only [Finset.sum_mul]
    have hiL (i : Fin n) : Integrable (fun x =>
        rawWeakSourceAdjoint d.potential (u i) (Du i i) i x * χ x)
        (potentialMeasure d.potential) := (hδ i).integrable_mul hχ2
    have hiR (i : Fin n) : Integrable (fun x => u i x * coordinateDerivative χ i x)
        (potentialMeasure d.potential) := (hdom i).1.integrable_mul (hDχ2 i)
    rw [integral_finsetSum Finset.univ (fun i _ => hiL i),
      integral_finsetSum Finset.univ (fun i _ => hiR i)]
    exact Finset.sum_congr rfl fun i _ => hi i
  have hApair {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) :
      (∫ x, actualSourceOperator d ψ x * χ x ∂potentialMeasure d.potential) =
        ∫ x, (∑ i : Fin n, u i x * coordinateDerivative χ i x) ∂potentialMeasure d.potential := by
    have hi := d.compact_metric_first_factor (fun j =>
      (contDiff_coordinateDerivative hψ (m := 1) (by norm_num) j).locallyLipschitz) hχ hχc
    calc
      _ = -(∫ x, χ x * hessianMetricDiffusion d.potential d.targetPotential ψ x
          ∂potentialMeasure d.potential) := by
        rw [← integral_neg]
        apply integral_congr_ae
        exact Eventually.of_forall fun _ => by dsimp [actualSourceOperator]; ring
      _ = _ := by
        rw [hi.2.2, neg_neg]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          dsimp [u, actualInverseGradient]
          simp only [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
  have hzero : ∀ᵐ x ∂potentialMeasure d.potential, δu x - actualSourceOperator d ψ x = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hδu.sub hA).integrable (by norm_num)).locallyIntegrable
    intro χ hχ hχc
    have hχ2 := memLp_of_continuous_hasCompactSupport d.source_C1.continuous hχ.continuous hχc
    have he : (∫ x, (δu x - actualSourceOperator d ψ x) * χ x ∂potentialMeasure d.potential) = 0 := by
      simp only [sub_mul]
      have hiδ : Integrable (fun x => δu x * χ x) (potentialMeasure d.potential) :=
        hδu.integrable_mul hχ2
      have hiA : Integrable (fun x => actualSourceOperator d ψ x * χ x)
          (potentialMeasure d.potential) := hA.integrable_mul hχ2
      rw [integral_sub hiδ hiA,
        hpair (hχ.of_le (by simp)) hχc, hApair (hχ.of_le (by simp)) hχc, sub_self]
    simpa only [smul_eq_mul, Pi.sub_apply, mul_comm] using he
  exact hzero.mono fun x hx => sub_eq_zero.mp hx

/-- The compact canonical generator has the actual signed source
Bochner norm on the genuine inverse-gradient coordinates. -/
theorem compact_actual_canonical_prebochner (d : SourceData μ)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    (∫ x, actualSourceOperator d ψ x ^ 2 ∂potentialMeasure d.potential) =
      ∫ x, ∑ i : Fin n, ∑ j : Fin n,
        (coordinateHessian d.potential x i j * actualInverseGradient d ψ i x *
          actualInverseGradient d ψ j x + actualInverseGradientDerivative d ψ i j x *
            actualInverseGradientDerivative d ψ j i x) ∂potentialMeasure d.potential := by
  have hd (i : Fin n) := inverseGradient_weighted_H1 d (hψ.of_le (by norm_num)) hc i
  have hb := integral_compact_rawWeak_source_vector_adjoint_square d.source_C1 d.source_lipschitz
    d.gradient_lipschitz (actualInverseGradient d ψ) (actualInverseGradientDerivative d ψ)
    (inverseGradient_compact d hc) (fun i => (hd i).1) (fun i j => ((hd i).2 j).1)
    (inverseGradientDerivative_compact d hc) (fun i j => ((hd i).2 j).2)
  have hsq := (inverseGradient_adjoint_eq_operator_ae d hψ hc).mono
    (fun x hx => congrArg (fun t : ℝ => t ^ 2) hx)
  rw [integral_congr_ae hsq] at hb
  exact hb

end KLSConstantImprovement.ActualSourceCompactCanonicalBochner405

#print axioms KLSConstantImprovement.ActualSourceCompactCanonicalBochner405.inverseGradient_adjoint_eq_operator_ae
#print axioms KLSConstantImprovement.ActualSourceCompactCanonicalBochner405.compact_actual_canonical_prebochner

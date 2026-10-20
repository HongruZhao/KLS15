import KLSConstantImprovement.ActualBoundedProductStein405
import KLSConstantImprovement.ActualCyclicRowAdjointAlgebra405
import KLSConstantImprovement.ActualQuadraticHessianDomains405
import KLSConstantImprovement.ActualQuadraticRowEll405

/-! The cyclic first adjoint on the actual quadratic natural inverse.
Global source Stein uses its genuine ordinary Hessian, and full T/N
symmetry identifies the signed derivative-H term with the same row ell. -/
noncomputable section
open MeasureTheory Matrix Set Filter
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualQuadraticCyclicAdjoint405
open KLS ActualBoundedCanonicalSource ActualBoundedRawTestAlgebra405 ActualBoundedRawSourceCalculus405
open ActualBoundedProductStein405 ActualCyclicRowAdjointAlgebra405 ActualQuadraticHessianDomains405
open ActualSourceQuadraticEta405 ActualQuadraticResponseField405 ActualQuadraticHilbertMatrix405
open ActualSourceNaturalTargetCurvatureDomain405 ActualQuadraticRowEll405 ActualAffineMatrixTests405
open ActualSourceHessianEvolution405 ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
variable {n : ℕ} {μ : Measure (Space n)}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

def actualQuadraticHessianPair (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  ∑ i, ∑ j, coordinateHessian d.potential x i j * (T i * actualQuadraticHessian d hn hμ (T j) x).trace

def actualQuadraticAffineCrossCost (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (x : Space n) : ℝ :=
  (coordinateHessian d.potential x * actualQuadraticFluxMatrix d T x * coordinateHessian d.potential x *
    (actualAffineMatrix d T x).transpose).trace

theorem actual_quadratic_cyclic_adjoint (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ j, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T j))) x ≤ C) :
    Integrable (actualQuadraticHessianPair d hn hμ T) (potentialMeasure d.potential) ∧
      Integrable (actualQuadraticAffineCrossCost d T) (potentialMeasure d.potential) ∧
      (∫ x, actualQuadraticHessianPair d hn hμ T x ∂potentialMeasure d.potential) =
        (∫ x, actualQuadraticAffineCrossCost d T x ∂potentialMeasure d.potential) -
          ∫ x, actualRowEll d T x ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let p (j a : Fin n) := naturalCanonicalRawGradient d (quadraticSourceDatum d (T j)) a
  have hp (j a : Fin n) : MemLp (p j a) 2 (potentialMeasure d.potential) := naturalCanonicalRawGradient_memLp d _ a
  have hD (j a b : Fin n) := actualQuadraticHessian_memLp d hn hμ (T j) hC (hM j) a b
  have hw (j a b : Fin n) := actualQuadraticHessian_weak d hn hμ (T j) hC (hM j) a b
  let Xterm : (Fin n × Fin n × Fin n × Fin n) → Space n → ℝ := fun q x =>
    T q.1 q.2.2.1 q.2.2.2 *
      (gradient d.potential x q.2.2.1 * coordinateHessian d.potential x q.1 q.2.1 * p q.2.1 q.2.2.2 x)
  let Nterm : (Fin n × Fin n × Fin n × Fin n) → Space n → ℝ := fun q x =>
    T q.1 q.2.2.1 q.2.2.2 * (d.third x q.2.2.1 q.1 q.2.1 * p q.2.1 q.2.2.2 x)
  let Cterm : (Fin n × Fin n × Fin n × Fin n) → Space n → ℝ := fun q x =>
    T q.1 q.2.2.1 q.2.2.2 * (coordinateHessian d.potential x q.1 q.2.1 *
      actualQuadraticHessian d hn hμ (T q.2.1) x q.2.2.2 q.2.2.1)
  have hXterm (q : Fin n × Fin n × Fin n × Fin n) : Integrable (Xterm q) (potentialMeasure d.potential) := by
    have hX : MemLp (fun x => gradient d.potential x q.2.2.1) ∞ (potentialMeasure d.potential) :=
      d.continuous_comp_gradient_memLp (EuclideanSpace.proj q.2.2.1).continuous ∞
    have hXH : MemLp (fun x => gradient d.potential x q.2.2.1 * coordinateHessian d.potential x q.1 q.2.1) ∞
        (potentialMeasure d.potential) := hX.mul (d.hessian_entry_memLp q.1 q.2.1 ∞)
    have hm : MemLp (fun x =>
        gradient d.potential x q.2.2.1 * coordinateHessian d.potential x q.1 q.2.1 *
          p q.2.1 q.2.2.2 x) 2 (potentialMeasure d.potential) :=
      hXH.mul (hp q.2.1 q.2.2.2)
    exact (hm.integrable (by norm_num)).const_mul _
  have hNterm (q : Fin n × Fin n × Fin n × Fin n) : Integrable (Nterm q) (potentialMeasure d.potential) := by
    have hN : MemLp (fun x => d.third x q.2.2.1 q.1 q.2.1) 2 (potentialMeasure d.potential) :=
      ActualBoundedRawSourceCalculus405.BoundedRawTest.ordinary_derivative_memLp
        (BoundedRawTest.hessian d q.1 q.2.1) q.2.2.1
    exact (hN.integrable_mul (hp q.2.1 q.2.2.2)).const_mul _
  have hCterm (q : Fin n × Fin n × Fin n × Fin n) : Integrable (Cterm q) (potentialMeasure d.potential) := by
    have hm : MemLp (fun x => coordinateHessian d.potential x q.1 q.2.1 *
        actualQuadraticHessian d hn hμ (T q.2.1) x q.2.2.2 q.2.2.1) 2
        (potentialMeasure d.potential) :=
      (d.hessian_entry_memLp q.1 q.2.1 ∞).mul (hD q.2.1 q.2.2.2 q.2.2.1)
    exact (hm.integrable (by norm_num)).const_mul _
  have hcomponent (q : Fin n × Fin n × Fin n × Fin n) :
      (∫ x, Cterm q x ∂potentialMeasure d.potential) =
        (∫ x, Xterm q x ∂potentialMeasure d.potential) - ∫ x, Nterm q x ∂potentialMeasure d.potential := by
    have hs := actual_global_bounded_product_stein d (BoundedRawTest.hessian d q.1 q.2.1)
      (hp q.2.1 q.2.2.2) (hD q.2.1 q.2.2.2) (hw q.2.1 q.2.2.2) q.2.2.1
    change (∫ x, gradient d.potential x q.2.2.1 * coordinateHessian d.potential x q.1 q.2.1 * p q.2.1 q.2.2.2 x
      ∂potentialMeasure d.potential) =
        (∫ x, d.third x q.2.2.1 q.1 q.2.1 * p q.2.1 q.2.2.2 x ∂potentialMeasure d.potential) +
          ∫ x, coordinateHessian d.potential x q.1 q.2.1 *
            actualQuadraticHessian d hn hμ (T q.2.1) x q.2.2.2 q.2.2.1 ∂potentialMeasure d.potential at hs
    dsimp only [Cterm, Xterm, Nterm]
    rw [integral_const_mul, integral_const_mul, integral_const_mul]
    have hscaled := congrArg (fun z : ℝ => T q.1 q.2.2.1 q.2.2.2 * z) hs
    linarith only [hscaled]
  have hsum : (∫ x, ∑ q, Cterm q x ∂potentialMeasure d.potential) =
      (∫ x, ∑ q, Xterm q x ∂potentialMeasure d.potential) - ∫ x, ∑ q, Nterm q x ∂potentialMeasure d.potential := by
    rw [integral_finsetSum Finset.univ (fun q _ => hCterm q),
      integral_finsetSum Finset.univ (fun q _ => hXterm q),
      integral_finsetSum Finset.univ (fun q _ => hNterm q)]
    simp_rw [hcomponent, Finset.sum_sub_distrib]
  have hCeq (x : Space n) : (∑ q, Cterm q x) = actualQuadraticHessianPair d hn hμ T x := by
    simp only [Fintype.sum_prod_type, Cterm, actualQuadraticHessianPair, Matrix.trace,
      Matrix.diag_apply, Matrix.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hXeq : (fun x => ∑ q, Xterm q x) =ᵐ[potentialMeasure d.potential] actualQuadraticAffineCrossCost d T := by
    filter_upwards [d.hessian_ae_source, ae_all_iff.mpr fun j =>
      hessian_mul_naturalCanonicalFlux_ae d (quadraticSourceDatum d (T j))] with x hx hpp
    have hrow : actualQuadraticFluxMatrix d T x * coordinateHessian d.potential x = Matrix.of (fun j a => p j a x) := by
      ext j a
      have he := congrFun (hpp j) a
      change (∑ b, quadraticRowFlux d T j b x * coordinateHessian d.potential x b a) =
        naturalCanonicalRawGradient d (quadraticSourceDatum d (T j)) a x
      rw [← he]
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro b _
      rw [hx.1.isHermitian.isSymm.apply a b]
      unfold quadraticRowFlux
      ring
    have he : (∑ q, Xterm q x) = ∑ i, ∑ j, ∑ a, ∑ b,
        T i a b * gradient d.potential x a * coordinateHessian d.potential x i j * p j b x := by
      simp only [Fintype.sum_prod_type, Xterm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    rw [he, full_tensor_affine_cross _ _ _ _ h12]
    symm
    rw [actualQuadraticAffineCrossCost, trace_metric_row_pair, hrow]
    rfl
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  have hNeq : (fun x => ∑ q, Nterm q x) =ᵐ[potentialMeasure d.potential] actualRowEll d T := by
    filter_upwards [d.third_symmetric_ae.filter_mono hac.ae_le, actualRowEll_gradient_ae d T] with x hN hell
    have he : (∑ q, Nterm q x) = ∑ i, ∑ j, ∑ a, ∑ b, T i a b * d.third x a i j * p j b x := by
      simp only [Fintype.sum_prod_type, Nterm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    rw [he]
    have hs := full_tensor_cyclic_cross T (sourceThirdMatrix d x) h12 h23
      (fun i j k => (hN i j k).1) (fun i j k => (hN i j k).2) (Matrix.of fun j a => p j a x)
    exact hs.trans hell.symm
  refine ⟨(integrable_finsetSum Finset.univ (fun q _ => hCterm q)).congr (Eventually.of_forall hCeq),
    (integrable_finsetSum Finset.univ (fun q _ => hXterm q)).congr hXeq, ?_⟩
  rw [integral_congr_ae (Eventually.of_forall hCeq), integral_congr_ae hXeq, integral_congr_ae hNeq] at hsum
  exact hsum

end KLSConstantImprovement.ActualQuadraticCyclicAdjoint405
#print axioms KLSConstantImprovement.ActualQuadraticCyclicAdjoint405.actual_quadratic_cyclic_adjoint

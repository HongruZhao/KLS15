import KLSConstantImprovement.ActualSourceNaturalTargetCurvatureDomain405
import KLSConstantImprovement.ActualSourceConnectionPointwise405
import KLSConstantImprovement.ActualSourceBoundedMassCutoffs405
import KLS.LocalWeakProduct

/-! Literal weak Hessian of the natural inverse under bounded mass.
The source Hessian is differentiated by its genuine third tensor; its
classical fderiv is never used. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff NNReal ENNReal
namespace KLSConstantImprovement.ActualSourceNaturalHessian405
open KLS ActualBoundedCanonicalSource ActualSourceHessianEvolution405 ActualSourceConnectionFields405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405 ActualSourceBoundedMassCutoffs405
open ActualSourceNaturalTargetCurvatureDomain405 ActualSourceConnectionPointwise405
open ActualSourceMetricFaithfulness405 ActualCanonicalMetricEnergyGraph
open ActualWeakCanonicalMetricInverse ActualWeakCanonicalMetricOrdinaryGraph
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

def naturalCanonicalHessian (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  coordinateHessian d.potential x * Matrix.of (fun i j => Du i j x) +
    sourceThirdAlong d (naturalCanonicalFlux d g) x

def naturalCanonicalHessianEnergy (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) (x : Space n) : ℝ :=
  ((coordinateHessian d.potential x)⁻¹ * naturalCanonicalHessian d g Du x *
    (coordinateHessian d.potential x)⁻¹ * naturalCanonicalHessian d g Du x).trace

theorem naturalCanonicalRawGradient_is_weak_derivative (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (i : Fin n) :
    HasLocalWeakCoordinateDerivative (sourceMetricInverse d g) (naturalCanonicalRawGradient d g i) i := by
  have he := (volume_absolutelyContinuous_potentialMeasure d.source_C1.continuous).ae_eq
    (sourceOrdinaryH1Embedding_derivative_ae d (sourceMetricInverseH1 d g) i)
  intro ψ hψ hc
  calc
    _ = -(∫ x, weightedH1Derivative d.potential i
        (sourceOrdinaryH1Embedding d (sourceMetricInverseH1 d g)) x * ψ x) :=
      sourceMetricInverse_unweighted_weak_identity d g hψ hc i
    _ = _ := congrArg Neg.neg (integral_congr_ae (he.fun_mul EventuallyEq.rfl))

theorem naturalCanonicalHessian_local_L2 (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d g) x ≤ C)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hDu : ∀ i j E, IsCompact E → MemLp (Du i j) 2 (volume.restrict E))
    (i j : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (fun x => naturalCanonicalHessian d g Du x i j) 2 (volume.restrict E) := by
  have hH (a b : Fin n) : MemLp (fun x => coordinateHessian d.potential x a b) ∞ (volume.restrict E) :=
    memLp_top_actual_hessian_of_locallyLipschitz_gradient d.gradient_lipschitz.locallyLipschitz a b hE
  have hu (a : Fin n) : MemLp (naturalCanonicalFlux d g a) ∞ (volume.restrict E) :=
    naturalCanonicalFlux_local_top_of_mass_bound d g hC hM a hE
  have hprod : MemLp (fun x => ∑ a : Fin n, coordinateHessian d.potential x i a * Du a j x)
      2 (volume.restrict E) := memLp_finsetSum Finset.univ fun a _ => (hH i a).mul (hDu a j E hE)
  have hN : MemLp (fun x => ∑ a : Fin n, naturalCanonicalFlux d g a x * d.third x a i j)
      2 (volume.restrict E) := memLp_finsetSum Finset.univ fun a _ => (hu a).mul (d.third_local_L2 a i j E hE)
  have hm := hprod.add hN
  change MemLp (fun x => (∑ a : Fin n, coordinateHessian d.potential x i a * Du a j x) +
    (∑ a : Fin n, naturalCanonicalFlux d g a x * d.third x a i j)) 2 (volume.restrict E) at hm
  simpa only [naturalCanonicalHessian, sourceThirdAlong, sourceThirdMatrix, Matrix.add_apply,
    Matrix.mul_apply, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using hm

theorem naturalCanonicalRawGradient_hasLocalWeakDerivative (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d g) x ≤ C)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i j E, IsCompact E → MemLp (Du i j) 2 (volume.restrict E))
    (hw : ∀ i j, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i j) j)
    (i j : Fin n) :
    HasLocalWeakCoordinateDerivative (naturalCanonicalRawGradient d g i)
      (fun x => naturalCanonicalHessian d g Du x i j) j := by
  let u := naturalCanonicalFlux d g
  let f (a : Fin n) (x : Space n) := coordinateHessian d.potential x i a * u a x
  let F (a : Fin n) (x : Space n) := d.third x j i a * u a x + coordinateHessian d.potential x i a * Du a j x
  have hH (a : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => coordinateHessian d.potential x i a) ∞ (volume.restrict E) :=
    memLp_top_actual_hessian_of_locallyLipschitz_gradient d.gradient_lipschitz.locallyLipschitz i a hE
  have huTop (a : Fin n) (E : Set (Space n)) (hE : IsCompact E) : MemLp (u a) ∞ (volume.restrict E) :=
    naturalCanonicalFlux_local_top_of_mass_bound d g hC hM a hE
  have hfloc (a : Fin n) (E : Set (Space n)) (hE : IsCompact E) : MemLp (f a) 2 (volume.restrict E) :=
    (hH a E hE).mul (hu a E hE)
  have hFloc (a : Fin n) (E : Set (Space n)) (hE : IsCompact E) : MemLp (F a) 2 (volume.restrict E) :=
    ((d.third_local_L2 j i a E hE).mul (huTop a E hE)).add ((hH a E hE).mul (hDu a j E hE))
  have hfw (a : Fin n) : HasLocalWeakCoordinateDerivative (f a) (F a) j :=
    (d.third_weak_derivative j i a).mul (hw a j)
      (memLp_two_on_compacts_of_top (hH a)) (hu a) (d.third_local_L2 j i a) (hDu a j)
  have hsum := hasLocalWeakCoordinateDerivative_finset_sum Finset.univ (fun a _ => hfw a)
    (fun a _ => locallyIntegrable_of_memLp_two_on_compacts (hfloc a))
    (fun a _ => locallyIntegrable_of_memLp_two_on_compacts (hFloc a))
  have hp : (fun x => ∑ a : Fin n, f a x) =ᵐ[(volume : Measure (Space n))]
      naturalCanonicalRawGradient d g i := by
    have he := (volume_absolutelyContinuous_potentialMeasure d.source_C1.continuous).ae_eq
      (hessian_mul_naturalCanonicalFlux_ae d g)
    filter_upwards [he] with x hx
    exact congrFun hx i
  have hF : (fun x => ∑ a : Fin n, F a x) =ᵐ[(volume : Measure (Space n))]
      fun x => naturalCanonicalHessian d g Du x i j := by
    filter_upwards [d.third_symmetric_ae] with x hx
    have hn (a : Fin n) : d.third x j i a = d.third x a i j := by
      calc
        _ = d.third x i j a := (hx j i a).1
        _ = d.third x i a j := (hx i j a).2
        _ = _ := (hx i a j).1
    simp only [F, naturalCanonicalHessian, sourceThirdAlong, sourceThirdMatrix,
      Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun a _ => by rw [hn a, mul_comm]
  exact hsum.congr_ae hp hF

theorem naturalCanonicalHessian_isSymm_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hc : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i j => Du i j x)).IsSymm) :
    ∀ᵐ x ∂potentialMeasure d.potential, (naturalCanonicalHessian d g Du x).IsSymm := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  filter_upwards [hc.filter_mono hac.ae_le, sourceThirdAlong_isSymm_ae d (naturalCanonicalFlux d g)] with x hD hN
  change (coordinateHessian d.potential x * Matrix.of (fun i j => Du i j x) +
    sourceThirdAlong d (naturalCanonicalFlux d g) x).transpose = _
  rw [Matrix.transpose_add, hD.eq, hN.eq]
  rfl

theorem naturalCanonicalHessianEnergy_eq_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) :
    naturalCanonicalHessianEnergy d g Du =ᵐ[potentialMeasure d.potential]
      fun x => sourceVectorJacobianEnergy Du x +
        sourceConnectionCross d (naturalCanonicalFlux d g) Du x +
        sourceConnectionGamma d (naturalCanonicalFlux d g) x := by
  filter_upwards [d.hessian_ae_source,
    sourceConnectionCross_eq_trace_ae d (naturalCanonicalFlux d g) Du] with x hp hX
  let H := coordinateHessian d.potential x
  let J := H⁻¹
  let B : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j => Du i j x)
  let N := sourceThirdAlong d (naturalCanonicalFlux d g) x
  have hJH : J * H = 1 := Matrix.nonsing_inv_mul H ((Matrix.isUnit_iff_isUnit_det _).mp hp.1.isUnit)
  have he : J * (H * B + N) = B + J * N := by
    rw [Matrix.mul_add, ← Matrix.mul_assoc, hJH, Matrix.one_mul]
  have htr : (J * N * B).trace = (B * J * N).trace := by
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hQ : (B * B).trace = sourceVectorJacobianEnergy Du x := by
    simp only [B, sourceVectorJacobianEnergy, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
  change (J * (H * B + N) * J * (H * B + N)).trace = _
  calc
    _ = ((B + J * N) * (B + J * N)).trace := by
      have hh : J * (H * B + N) * J * (H * B + N) =
          (J * (H * B + N)) * (J * (H * B + N)) := by simp only [Matrix.mul_assoc]
      rw [hh, he]
    _ = (B * B).trace + 2 * (B * J * N).trace + (J * N * J * N).trace := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.trace_add]
      rw [htr]
      simp only [Matrix.mul_assoc]
      ring
    _ = _ := by rw [hQ, ← hX, sourceThirdAlong_trace_square]

end KLSConstantImprovement.ActualSourceNaturalHessian405
#print axioms KLSConstantImprovement.ActualSourceNaturalHessian405.naturalCanonicalRawGradient_is_weak_derivative
#print axioms KLSConstantImprovement.ActualSourceNaturalHessian405.naturalCanonicalHessian_local_L2
#print axioms KLSConstantImprovement.ActualSourceNaturalHessian405.naturalCanonicalRawGradient_hasLocalWeakDerivative
#print axioms KLSConstantImprovement.ActualSourceNaturalHessian405.naturalCanonicalHessian_isSymm_ae
#print axioms KLSConstantImprovement.ActualSourceNaturalHessian405.naturalCanonicalHessianEnergy_eq_ae

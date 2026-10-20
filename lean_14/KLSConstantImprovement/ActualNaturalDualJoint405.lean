import KLSConstantImprovement.ActualNaturalLocalHessianDomain405
import KLSConstantImprovement.ActualJointBumpControl405
import KLSConstantImprovement.ActualNaturalRowEnergyLocal405
import KLSConstantImprovement.ActualSourceRawHessianEvolution405

/-! Common joint nonlinear tests in the ACTUAL natural flux u and its
ordinary gradient p=Hu. Both vectors are now genuine local H1. Their mass
is the literal bilinear u dot p, so its joint directional derivative is
exactly the already proved raw weak mass derivative. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal NNReal
namespace KLSConstantImprovement.ActualNaturalDualJoint405
open KLS ActualBoundedCanonicalSource ActualSourceNaturalGaffney405
open ActualSourceNaturalTargetCurvatureDomain405 ActualSourceNaturalHessian405
open ActualNaturalLocalHessianDomain405 ActualVectorDifferential405 ActualLocalWeakVectorChain405
open ActualNaturalRowEnergyLocal405 ActualBoundedRawMetricDomain ActualSourceRawHessianEvolution405
open ActualSmoothScalarTruncation405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

abbrev DualIndex (n : ℕ) := Sum (Fin n) (Fin n)

def dualMass (v : DualIndex n → ℝ) : ℝ := ∑ i : Fin n, v (.inl i) * v (.inr i)

def dualBump (k : ℕ) (v : DualIndex n → ℝ) : ℝ :=
  ∏ a : DualIndex n, scalarBump (cutoffScale k * v a)

def dualValue (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (a : DualIndex n) (x : Space n) : ℝ :=
  Sum.elim (fun i => naturalCanonicalFlux d g i x) (fun i => naturalCanonicalRawGradient d g i x) a

def dualDerivative (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) (a : DualIndex n) (b : Fin n) (x : Space n) : ℝ :=
  Sum.elim (fun i => Du i b x) (fun i => naturalCanonicalHessian d g Du x i b) a

def dualSource (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (η : (DualIndex n → ℝ) → ℝ) (x : Space n) : ℝ := η (fun a => dualValue d g a x)

def dualSourceDerivative (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) (η : (DualIndex n → ℝ) → ℝ)
    (b : Fin n) (x : Space n) : ℝ :=
  fderiv ℝ η (fun a => dualValue d g a x) (fun a => dualDerivative d g Du a b x)

theorem actual_dual_compact_chain (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i b E, IsCompact E → MemLp (Du i b) 2 (volume.restrict E))
    (hw : ∀ i b, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i b) b)
    (hC : ∀ i b E, IsCompact E → MemLp (fun x => naturalCanonicalHessian d g Du x i b) 2 (volume.restrict E))
    {η : (DualIndex n → ℝ) → ℝ} (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) :
    (∃ B : ℝ, ∀ x, ‖dualSource d g η x‖ ≤ B) ∧
      (∀ E, IsCompact E → MemLp (dualSource d g η) 2 (volume.restrict E)) ∧
      (∀ b E, IsCompact E → MemLp (dualSourceDerivative d g Du η b) 2 (volume.restrict E)) ∧
      ∀ b, HasLocalWeakCoordinateDerivative (dualSource d g η) (dualSourceDerivative d g Du η b) b := by
  have hv (a : DualIndex n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (dualValue d g a) 2 (volume.restrict E) := by
    cases a with
    | inl i => exact hu i E hE
    | inr i =>
        exact KLS.MemLp.restrict_volume_of_potentialMeasure
          (naturalCanonicalRawGradient_memLp d g i) d.source_C1.continuous hE
  have hF (a : DualIndex n) (b : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (dualDerivative d g Du a b) 2 (volume.restrict E) := by
    cases a with
    | inl i => exact hDu i b E hE
    | inr i => exact hC i b E hE
  have hW (a : DualIndex n) (b : Fin n) :
      HasLocalWeakCoordinateDerivative (dualValue d g a) (dualDerivative d g Du a b) b := by
    cases a with
    | inl i => exact hw i b
    | inr i => exact naturalRawGradient_weakHessian_without_mass d g Du hu hDu hw i b
  obtain ⟨B, hB⟩ := hcη.exists_bound_of_continuous hη.continuous
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcη hη (by norm_num)
  have ht (E : Set (Space n)) (hE : IsCompact E) : MemLp (dualSource d g η) ∞ (volume.restrict E) := by
    apply memLp_top_of_bound
      (hη.continuous.comp_aestronglyMeasurable (MemLp.of_eval fun a => hv a E hE).aestronglyMeasurable) B
    exact Eventually.of_forall fun x => hB _
  refine ⟨⟨B, fun x => hB _⟩, memLp_two_on_compacts_of_top ht, ?_, ?_⟩
  · intro b E hE
    have he := vector_composed_derivative_local_L2 hv (fun a => hF a b) hη hL E hE
    exact (memLp_congr_ae (Eventually.of_forall fun x => (fderiv_eq_sum_vectorPartial η _ _).symm)).mp he
  · intro b
    have he := local_vector_chain hv (fun a => hF a b) (fun a => hW a b) hη hL
    exact he.congr_ae EventuallyEq.rfl (Eventually.of_forall fun x => (fderiv_eq_sum_vectorPartial η _ _).symm)

theorem actual_dual_compact_source_test (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i b E, IsCompact E → MemLp (Du i b) 2 (volume.restrict E))
    (hw : ∀ i b, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i b) b)
    (hC : ∀ i b E, IsCompact E → MemLp (fun x => naturalCanonicalHessian d g Du x i b) 2 (volume.restrict E))
    {η : (DualIndex n → ℝ) → ℝ} (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∀ E, IsCompact E → MemLp (fun x => ψ x * dualSource d g η x) 2 (volume.restrict E)) ∧
      HasCompactSupport (fun x => ψ x * dualSource d g η x) ∧
      (∃ B : ℝ, ∀ᵐ x ∂volume, ‖ψ x * dualSource d g η x‖ ≤ B) ∧
      (∀ a E, IsCompact E → MemLp (rawCutoffDerivative ψ (dualSource d g η)
        (dualSourceDerivative d g Du η) a) 2 (volume.restrict E)) ∧
      ∀ a, HasLocalWeakCoordinateDerivative (fun x => ψ x * dualSource d g η x)
        (rawCutoffDerivative ψ (dualSource d g η) (dualSourceDerivative d g Du η) a) a := by
  obtain ⟨⟨B, hB⟩, hv, hD, hW⟩ := actual_dual_compact_chain d g Du hu hDu hw hC hη hcη
  obtain ⟨C, hCc⟩ := hc.exists_bound_of_continuous hψ.continuous
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hCc 0)
  refine ⟨fun E hE => memLp_continuous_mul_on_compact hE (hv E hE) hψ.continuous,
    hc.mul_right, ⟨C * B, Eventually.of_forall fun x => ?_⟩, ?_, ?_⟩
  · rw [norm_mul]
    exact mul_le_mul (hCc x) (hB x) (norm_nonneg _) hC0
  · intro a E hE
    exact (memLp_continuous_mul_on_compact hE (hD a E hE) hψ.continuous).add
      (memLp_continuous_mul_on_compact hE (hv E hE)
        (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) a).continuous)
  · intro a
    obtain ⟨W, hweak, he⟩ := (hW a).compact_mul hv (hD a) hψ hc
    exact (show HasLocalWeakCoordinateDerivative (fun x => ψ x * dualSource d g η x)
      (fun x => W x) a from hweak).congr_ae EventuallyEq.rfl he

theorem dualMass_differential (v z : DualIndex n → ℝ) :
    fderiv ℝ (dualMass (n := n)) v z =
      ∑ i : Fin n, (z (.inl i) * v (.inr i) + v (.inl i) * z (.inr i)) := by
  have hv (a : DualIndex n) : HasFDerivAt (fun y : DualIndex n → ℝ => y a)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : DualIndex n => ℝ) a) v :=
    hasFDerivAt_apply a v
  have hh := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => (hv (.inl i)).mul (hv (.inr i))
  have hfun : (fun a : DualIndex n → ℝ => ∑ c : Fin n,
      ((fun y : DualIndex n → ℝ => y (Sum.inl c)) *
        (fun y : DualIndex n → ℝ => y (Sum.inr c))) a) = dualMass := by
    funext a
    simp only [dualMass, Pi.mul_apply]
  rw [hfun] at hh
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

end KLSConstantImprovement.ActualNaturalDualJoint405
#print axioms KLSConstantImprovement.ActualNaturalDualJoint405.actual_dual_compact_chain
#print axioms KLSConstantImprovement.ActualNaturalDualJoint405.actual_dual_compact_source_test
#print axioms KLSConstantImprovement.ActualNaturalDualJoint405.dualMass_differential

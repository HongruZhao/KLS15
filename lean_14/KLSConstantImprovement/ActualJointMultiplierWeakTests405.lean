import KLSConstantImprovement.ActualIntrinsicSourceCompactRange405
import KLSConstantImprovement.ActualNaturalRowEnergyLocal405
import KLSConstantImprovement.ActualSourceRawHessianEvolution405

/-! Actual compact joint multipliers for nonlinear row and H-evolution
testing. The joint variables are the genuine weak flux u and the raw source
Hessian H. Compactification is in all joint variables, so row/matrix
products have bounded values and genuine local H1 derivatives. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal NNReal
namespace KLSConstantImprovement.ActualJointMultiplierWeakTests405
open KLS ActualBoundedCanonicalSource ActualIntrinsicJointWeakTests405 ActualIntrinsicSourceCompactRange405
open ActualVectorDifferential405 ActualLocalWeakVectorChain405 ActualSourceNaturalGaffney405
open ActualNaturalRowEnergyLocal405 ActualSourceRawHessianEvolution405
open ActualBoundedRawMetricDomain ActualSourceHessianEvolution405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

def jointSource (d : SourceData μ) (u : Fin n → Space n → ℝ)
    (η : (JointIndex n → ℝ) → ℝ) (x : Space n) : ℝ :=
  η (fun a => sourceJointValue d u a x)

def jointSourceDerivative (d : SourceData μ) (u : Fin n → Space n → ℝ)
    (Du : Fin n → Fin n → Space n → ℝ) (η : (JointIndex n → ℝ) → ℝ)
    (b : Fin n) (x : Space n) : ℝ :=
  fderiv ℝ η (fun a => sourceJointValue d u a x) (fun a => sourceJointDerivative d Du a b x)

def jointRow (η : (JointIndex n → ℝ) → ℝ) (i : Fin n) (v : JointIndex n → ℝ) : ℝ :=
  η v * v (.inl i)

def jointMatrix (η : (JointIndex n → ℝ) → ℝ) (i j : Fin n) (v : JointIndex n → ℝ) : ℝ :=
  η v * (v (.inl i) * v (.inl j))

theorem actual_compact_joint_domains (d : SourceData μ)
    {u : Fin n → Space n → ℝ} {Du : Fin n → Fin n → Space n → ℝ}
    (hu : ∀ i E, IsCompact E → MemLp (u i) 2 (volume.restrict E))
    (hDu : ∀ i b E, IsCompact E → MemLp (Du i b) 2 (volume.restrict E))
    (hw : ∀ i b, HasLocalWeakCoordinateDerivative (u i) (Du i b) b)
    {η : (JointIndex n → ℝ) → ℝ} (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) :
    (∃ B : ℝ, ∀ x, ‖jointSource d u η x‖ ≤ B) ∧
      (∀ E, IsCompact E → MemLp (jointSource d u η) 2 (volume.restrict E)) ∧
      (∀ b E, IsCompact E → MemLp (jointSourceDerivative d u Du η b) 2 (volume.restrict E)) ∧
      ∀ b, HasLocalWeakCoordinateDerivative (jointSource d u η) (jointSourceDerivative d u Du η b) b := by
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hη.continuous
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hη (by norm_num)
  have hv := sourceJointValue_local_L2 d hu
  have hD := sourceJointDerivative_local_L2 d hDu
  have hW (a : JointIndex n) (b : Fin n) :
      HasLocalWeakCoordinateDerivative (sourceJointValue d u a) (sourceJointDerivative d Du a b) b := by
    cases a with
    | inl i => exact hw i b
    | inr ij => exact d.third_weak_derivative b ij.1 ij.2
  have ht (E : Set (Space n)) (hE : IsCompact E) : MemLp (jointSource d u η) ∞ (volume.restrict E) := by
    apply memLp_top_of_bound
      (hη.continuous.comp_aestronglyMeasurable (MemLp.of_eval fun a => hv a E hE).aestronglyMeasurable) B
    exact Eventually.of_forall fun x => hB _
  refine ⟨⟨B, fun x => hB _⟩, memLp_two_on_compacts_of_top ht, ?_, ?_⟩
  · intro b E hE
    have he := vector_composed_derivative_local_L2 hv (fun a => hD a b) hη hL E hE
    apply (memLp_congr_ae (Eventually.of_forall fun x =>
      (fderiv_eq_sum_vectorPartial η _ _).symm)).mp he
  · intro b
    have he := local_vector_chain hv (fun a => hD a b) (fun a => hW a b) hη hL
    exact he.congr_ae EventuallyEq.rfl (Eventually.of_forall fun x =>
      (fderiv_eq_sum_vectorPartial η _ _).symm)

theorem jointRow_contDiff_compact {η : (JointIndex n → ℝ) → ℝ}
    (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) (i : Fin n) :
    ContDiff ℝ 1 (jointRow η i) ∧ HasCompactSupport (jointRow η i) :=
  ⟨hη.mul (contDiff_apply ℝ ℝ (Sum.inl i : JointIndex n)), hc.mul_right⟩

theorem jointMatrix_contDiff_compact {η : (JointIndex n → ℝ) → ℝ}
    (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) (i j : Fin n) :
    ContDiff ℝ 1 (jointMatrix η i j) ∧ HasCompactSupport (jointMatrix η i j) :=
  ⟨hη.mul ((contDiff_apply ℝ ℝ (Sum.inl i : JointIndex n)).mul (contDiff_apply ℝ ℝ (Sum.inl j : JointIndex n))), hc.mul_right⟩

theorem jointRow_differential {η : (JointIndex n → ℝ) → ℝ}
    (hη : ContDiff ℝ 1 η) (i : Fin n) (v w : JointIndex n → ℝ) :
    fderiv ℝ (jointRow η i) v w = η v * w (.inl i) + v (.inl i) * fderiv ℝ η v w := by
  change fderiv ℝ (fun z => η z * z (.inl i)) v w = _
  rw [fderiv_fun_mul (hη.differentiable one_ne_zero v) (differentiableAt_apply (.inl i) v)]
  rw [(hasFDerivAt_apply (𝕜 := ℝ) (.inl i) v).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.proj_apply]

theorem jointMatrix_differential {η : (JointIndex n → ℝ) → ℝ}
    (hη : ContDiff ℝ 1 η) (i j : Fin n) (v w : JointIndex n → ℝ) :
    fderiv ℝ (jointMatrix η i j) v w =
      η v * (w (.inl i) * v (.inl j) + v (.inl i) * w (.inl j)) +
        (v (.inl i) * v (.inl j)) * fderiv ℝ η v w := by
  change fderiv ℝ (fun z => η z * (z (.inl i) * z (.inl j))) v w = _
  rw [fderiv_fun_mul (c := η)
    (d := fun z : JointIndex n → ℝ => z (Sum.inl i) * z (Sum.inl j))
    (hη.differentiable one_ne_zero v)
    ((differentiableAt_apply (.inl i) v).mul (differentiableAt_apply (.inl j) v))]
  rw [fderiv_fun_mul (c := fun z : JointIndex n → ℝ => z (Sum.inl i))
    (d := fun z : JointIndex n → ℝ => z (Sum.inl j))
    (differentiableAt_apply (.inl i) v) (differentiableAt_apply (.inl j) v)]
  rw [(hasFDerivAt_apply (𝕜 := ℝ) (.inl i) v).fderiv,
    (hasFDerivAt_apply (𝕜 := ℝ) (.inl j) v).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.proj_apply] <;> ring

theorem actual_compact_joint_multiplier_test (d : SourceData μ)
    {u : Fin n → Space n → ℝ} {Du : Fin n → Fin n → Space n → ℝ}
    (hu : ∀ i E, IsCompact E → MemLp (u i) 2 (volume.restrict E))
    (hDu : ∀ i b E, IsCompact E → MemLp (Du i b) 2 (volume.restrict E))
    (hw : ∀ i b, HasLocalWeakCoordinateDerivative (u i) (Du i b) b)
    {η : (JointIndex n → ℝ) → ℝ} (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∀ E, IsCompact E → MemLp (fun x => ψ x * jointSource d u η x) 2 (volume.restrict E)) ∧
      HasCompactSupport (fun x => ψ x * jointSource d u η x) ∧
      (∃ B : ℝ, ∀ᵐ x ∂volume, ‖ψ x * jointSource d u η x‖ ≤ B) ∧
      (∀ a E, IsCompact E → MemLp (rawCutoffDerivative ψ (jointSource d u η)
        (jointSourceDerivative d u Du η) a) 2 (volume.restrict E)) ∧
      ∀ a, HasLocalWeakCoordinateDerivative (fun x => ψ x * jointSource d u η x)
        (rawCutoffDerivative ψ (jointSource d u η) (jointSourceDerivative d u Du η) a) a := by
  obtain ⟨⟨B, hB⟩, hv, hD, hW⟩ := actual_compact_joint_domains d hu hDu hw hη hcη
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hψ.continuous
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨fun E hE => memLp_continuous_mul_on_compact hE (hv E hE) hψ.continuous,
    hc.mul_right, ⟨C * B, Eventually.of_forall fun x => ?_⟩, ?_, ?_⟩
  · rw [norm_mul]
    exact mul_le_mul (hC x) (hB x) (norm_nonneg _) hC0
  · intro a E hE
    exact (memLp_continuous_mul_on_compact hE (hD a E hE) hψ.continuous).add
      (memLp_continuous_mul_on_compact hE (hv E hE)
        (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) a).continuous)
  · intro a
    obtain ⟨W, hweak, he⟩ := (hW a).compact_mul hv (hD a) hψ hc
    exact (show HasLocalWeakCoordinateDerivative (fun x => ψ x * jointSource d u η x)
      (fun x => W x) a from hweak).congr_ae EventuallyEq.rfl he

theorem actual_joint_matrix_hessian_evolution (d : SourceData μ)
    {u : Fin n → Space n → ℝ} {Du : Fin n → Fin n → Space n → ℝ}
    (hu : ∀ i E, IsCompact E → MemLp (u i) 2 (volume.restrict E))
    (hDu : ∀ i b E, IsCompact E → MemLp (Du i b) 2 (volume.restrict E))
    (hw : ∀ i b, HasLocalWeakCoordinateDerivative (u i) (Du i b) b)
    {η : (JointIndex n → ℝ) → ℝ} (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (i j : Fin n) :
    (∀ a, Integrable (fun x => ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
      rawCutoffDerivative ψ (jointSource d u (jointMatrix η i j))
        (jointSourceDerivative d u Du (jointMatrix η i j)) a x) (potentialMeasure d.potential)) ∧
      Integrable (fun x => (-coordinateHessian d.potential x i j + sourceConnectionCurvature d x i j) *
        (ψ x * jointSource d u (jointMatrix η i j) x)) (potentialMeasure d.potential) ∧
      -(∑ a : Fin n, ∫ x, ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
        rawCutoffDerivative ψ (jointSource d u (jointMatrix η i j))
          (jointSourceDerivative d u Du (jointMatrix η i j)) a x ∂potentialMeasure d.potential) =
        ∫ x, (-coordinateHessian d.potential x i j + sourceConnectionCurvature d x i j) *
          (ψ x * jointSource d u (jointMatrix η i j) x) ∂potentialMeasure d.potential := by
  have hηm := jointMatrix_contDiff_compact hη hcη i j
  obtain ⟨hv, hcc, ⟨B, hb⟩, hD, hW⟩ := actual_compact_joint_multiplier_test d hu hDu hw
    hηm.1 hηm.2 hψ hc
  exact actual_compact_raw_hessian_evolution d hv hcc hb hD hW i j

end KLSConstantImprovement.ActualJointMultiplierWeakTests405
#print axioms KLSConstantImprovement.ActualJointMultiplierWeakTests405.actual_compact_joint_domains
#print axioms KLSConstantImprovement.ActualJointMultiplierWeakTests405.jointRow_differential
#print axioms KLSConstantImprovement.ActualJointMultiplierWeakTests405.jointMatrix_differential
#print axioms KLSConstantImprovement.ActualJointMultiplierWeakTests405.actual_compact_joint_multiplier_test
#print axioms KLSConstantImprovement.ActualJointMultiplierWeakTests405.actual_joint_matrix_hessian_evolution

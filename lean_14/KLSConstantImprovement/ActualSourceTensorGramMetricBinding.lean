import KLSConstantImprovement.ActualSourceHessianMetricBinding

/-!
Actual canonical form entries for G_T(H)_{ij}=Tr(T_i H T_j H).
All slices T_i are constant. Their symmetry is not needed for form membership.
The displayed gradient is the genuine weak product derivative in the actual
source Hessian and its weak third tensor, never a classical fderiv of H.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceTensorGramMetricBinding
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualCompactRawMetricGraph ActualBoundedRawMetricDomain
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def sourceTensorGramEntry (φ : Space n → ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (x : Space n) : ℝ :=
  ∑ a, ∑ e, ∑ c, ∑ b,
    (T i a b * T j c e) * (coordinateHessian φ x b c * coordinateHessian φ x e a)

def sourceTensorGramRawDerivative (φ : Space n → ℝ)
    (N : Space n → Fin n → Fin n → Fin n → ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j k : Fin n) (x : Space n) : ℝ :=
  ∑ a, ∑ e, ∑ c, ∑ b, (T i a b * T j c e) *
    (N x k b c * coordinateHessian φ x e a + coordinateHessian φ x b c * N x k e a)

theorem sourceTensorGramEntry_eq_trace (φ : Space n → ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (x : Space n) :
    sourceTensorGramEntry φ T i j x =
      (T i * coordinateHessian φ x * T j * coordinateHessian φ x).trace := by
  simp only [sourceTensorGramEntry, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro b _
  ring

private theorem weak_sum_localL2 {α : Type*} [Fintype α]
    {f F : α → Space n → ℝ} {k : Fin n}
    (hW : ∀ a, HasLocalWeakCoordinateDerivative (f a) (F a) k)
    (hf : ∀ a E, IsCompact E → MemLp (f a) 2 (volume.restrict E))
    (hF : ∀ a E, IsCompact E → MemLp (F a) 2 (volume.restrict E)) :
    HasLocalWeakCoordinateDerivative (fun x => ∑ a, f a x) (fun x => ∑ a, F a x) k := by
  exact hasLocalWeakCoordinateDerivative_finset_sum Finset.univ
    (fun a _ => hW a)
    (fun a _ => locallyIntegrable_of_memLp_two_on_compacts (hf a))
    (fun a _ => locallyIntegrable_of_memLp_two_on_compacts (hF a))

private theorem raw_metric_sum {α : Type*} [Fintype α]
    (φ : Space n → ℝ) (F : α → Fin n → Space n → ℝ) (r : Fin n) (x : Space n) :
    rawCanonicalMetricDerivative φ (fun k y => ∑ a, F a k y) r x =
      ∑ a, rawCanonicalMetricDerivative φ (F a) r x := by
  unfold rawCanonicalMetricDerivative
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

private theorem raw_metric_hessian_product (φ : Space n → ℝ)
    (N : Space n → Fin n → Fin n → Fin n → ℝ) (v : ℝ)
    (a b c e r : Fin n) (x : Space n) :
    rawCanonicalMetricDerivative φ
      (fun k y => v * (N y k b c * coordinateHessian φ y e a +
        coordinateHessian φ y b c * N y k e a)) r x =
      v * (coordinateHessian φ x e a *
        rawCanonicalMetricDerivative φ (fun k y => N y k b c) r x +
        coordinateHessian φ x b c *
        rawCanonicalMetricDerivative φ (fun k y => N y k e a) r x) := by
  unfold rawCanonicalMetricDerivative
  calc
    _ = ∑ k : Fin n,
        ((v * coordinateHessian φ x e a) * (canonicalMetricRoot φ x r k * N x k b c) +
        (v * coordinateHessian φ x b c) * (canonicalMetricRoot φ x r k * N x k e a)) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring

theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.tensorGram_derivative_local_L2
    {μ : Measure (Space n)} (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j k : Fin n)
    (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (sourceTensorGramRawDerivative d.potential d.third T i j k) 2 (volume.restrict E) := by
  unfold sourceTensorGramRawDerivative
  apply memLp_finsetSum
  intro a _
  apply memLp_finsetSum
  intro e _
  apply memLp_finsetSum
  intro c _
  apply memLp_finsetSum
  intro b _
  have hHbc := memLp_coordinateHessian_top_of_gradient_lipschitz d.gradient_lipschitz
    (volume.restrict E) b c
  have hHea := memLp_coordinateHessian_top_of_gradient_lipschitz d.gradient_lipschitz
    (volume.restrict E) e a
  have ha : MemLp (fun x => d.third x k b c * coordinateHessian d.potential x e a) 2
      (volume.restrict E) := by
    have hm : MemLp (fun x => coordinateHessian d.potential x e a * d.third x k b c) 2
        (volume.restrict E) := hHea.mul (d.third_local_L2 k b c E hE)
    exact (memLp_congr_ae (Eventually.of_forall fun x => mul_comm _ _)).mp hm
  exact (ha.add (hHbc.mul (d.third_local_L2 k e a E hE))).const_mul (T i a b * T j c e)

theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.tensorGram_hasLocalWeakCoordinateDerivative
    {μ : Measure (Space n)} (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j k : Fin n) :
    HasLocalWeakCoordinateDerivative (sourceTensorGramEntry d.potential T i j)
      (sourceTensorGramRawDerivative d.potential d.third T i j k) k := by
  let f (a e c b : Fin n) (x : Space n) :=
    (T i a b * T j c e) * (coordinateHessian d.potential x b c * coordinateHessian d.potential x e a)
  let F (a e c b : Fin n) (x : Space n) := (T i a b * T j c e) *
    (d.third x k b c * coordinateHessian d.potential x e a +
      coordinateHessian d.potential x b c * d.third x k e a)
  have hHloc (a b : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => coordinateHessian d.potential x a b) 2 (volume.restrict E) := by
    letI : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hE.measure_ne_top
    exact (memLp_coordinateHessian_top_of_gradient_lipschitz d.gradient_lipschitz
      (volume.restrict E) a b).mono_exponent (by simp)
  have hfl (a e c b : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (f a e c b) 2 (volume.restrict E) := by
    exact ((memLp_coordinateHessian_top_of_gradient_lipschitz d.gradient_lipschitz
      (volume.restrict E) b c).mul (hHloc e a E hE)).const_mul (T i a b * T j c e)
  have hFl (a e c b : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (F a e c b) 2 (volume.restrict E) := by
    have ha : MemLp (fun x => d.third x k b c * coordinateHessian d.potential x e a) 2
        (volume.restrict E) := by
      have hm : MemLp (fun x => coordinateHessian d.potential x e a * d.third x k b c) 2
          (volume.restrict E) :=
        (memLp_coordinateHessian_top_of_gradient_lipschitz d.gradient_lipschitz
          (volume.restrict E) e a).mul (d.third_local_L2 k b c E hE)
      exact (memLp_congr_ae (Eventually.of_forall fun x => mul_comm _ _)).mp hm
    exact (ha.add ((memLp_coordinateHessian_top_of_gradient_lipschitz d.gradient_lipschitz
      (volume.restrict E) b c).mul (d.third_local_L2 k e a E hE))).const_mul (T i a b * T j c e)
  have hw (a e c b : Fin n) : HasLocalWeakCoordinateDerivative (f a e c b) (F a e c b) k :=
    ((d.third_weak_derivative k b c).mul (d.third_weak_derivative k e a)
      (hHloc b c) (hHloc e a) (d.third_local_L2 k b c) (d.third_local_L2 k e a)).const_mul
      (T i a b * T j c e)
  have h1 (a e c : Fin n) := weak_sum_localL2 (hw a e c) (hfl a e c) (hFl a e c)
  have hfl1 (a e c : Fin n) (E : Set (Space n)) (hE : IsCompact E) :=
    memLp_finsetSum Finset.univ (fun b _ => hfl a e c b E hE)
  have hFl1 (a e c : Fin n) (E : Set (Space n)) (hE : IsCompact E) :=
    memLp_finsetSum Finset.univ (fun b _ => hFl a e c b E hE)
  have h2 (a e : Fin n) := weak_sum_localL2 (h1 a e) (hfl1 a e) (hFl1 a e)
  have hfl2 (a e : Fin n) (E : Set (Space n)) (hE : IsCompact E) :=
    memLp_finsetSum Finset.univ (fun c _ => hfl1 a e c E hE)
  have hFl2 (a e : Fin n) (E : Set (Space n)) (hE : IsCompact E) :=
    memLp_finsetSum Finset.univ (fun c _ => hFl1 a e c E hE)
  have h3 (a : Fin n) := weak_sum_localL2 (h2 a) (hfl2 a) (hFl2 a)
  have hfl3 (a : Fin n) (E : Set (Space n)) (hE : IsCompact E) :=
    memLp_finsetSum Finset.univ (fun e _ => hfl2 a e E hE)
  have hFl3 (a : Fin n) (E : Set (Space n)) (hE : IsCompact E) :=
    memLp_finsetSum Finset.univ (fun e _ => hFl2 a e E hE)
  exact weak_sum_localL2 h3 hfl3 hFl3

theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.tensorGram_raw_metric_memLp
    {μ : Measure (Space n)} (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j r : Fin n) :
    MemLp (rawCanonicalMetricDerivative d.potential
      (sourceTensorGramRawDerivative d.potential d.third T i j) r) 2
      (potentialMeasure d.potential) := by
  have he : rawCanonicalMetricDerivative d.potential
      (sourceTensorGramRawDerivative d.potential d.third T i j) r =
      fun x => ∑ a, ∑ e, ∑ c, ∑ b, (T i a b * T j c e) *
        (coordinateHessian d.potential x e a *
          rawCanonicalMetricDerivative d.potential (fun k y => d.third y k b c) r x +
         coordinateHessian d.potential x b c *
          rawCanonicalMetricDerivative d.potential (fun k y => d.third y k e a) r x) := by
    funext x
    unfold sourceTensorGramRawDerivative
    simp_rw [raw_metric_sum, raw_metric_hessian_product]
  rw [he]
  apply memLp_finsetSum
  intro a _
  apply memLp_finsetSum
  intro e _
  apply memLp_finsetSum
  intro c _
  apply memLp_finsetSum
  intro b _
  exact (((memLp_coordinateHessian_top_of_gradient_lipschitz d.gradient_lipschitz
    (potentialMeasure d.potential) e a).mul (d.hessian_entry_raw_metric_memLp b c r)).add
    ((memLp_coordinateHessian_top_of_gradient_lipschitz d.gradient_lipschitz
      (potentialMeasure d.potential) b c).mul (d.hessian_entry_raw_metric_memLp e a r))).const_mul
        (T i a b * T j c e)

theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.tensorGram_raw_energy_integrable
    {μ : Measure (Space n)} (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    Integrable (rawInverseHessianGradientForm d.potential
      (sourceTensorGramRawDerivative d.potential d.third T i j)) (potentialMeasure d.potential) := by
  have hi : Integrable (fun x => ∑ r,
      rawCanonicalMetricDerivative d.potential
        (sourceTensorGramRawDerivative d.potential d.third T i j) r x ^ 2)
      (potentialMeasure d.potential) :=
    integrable_finsetSum Finset.univ (fun r _ => (d.tensorGram_raw_metric_memLp T i j r).integrable_sq)
  exact hi.congr (d.raw_metric_derivative_sq_ae _)

theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.hessian_range_bounded
    {μ : Measure (Space n)} (d : SourceData μ) :
    Bornology.IsBounded (range (coordinateHessian d.potential)) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨16 / d.targetConvexityConstant, ?_⟩
  rintro _ ⟨x, rfl⟩
  apply (Matrix.norm_le_iff (div_nonneg (by norm_num) d.target_convexity_pos.le)).mpr
  intro a b
  exact coordinateHessian_entry_bound_of_gradient_lipschitz d.gradient_lipschitz x a b

/-- The literal tensor-Gram entry has all domains and its actual weak metric
gradient realized on the same canonical form graph. No G-form witness is input. -/
theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.exists_tensorGram_entry_metricH1
    {μ : Measure (Space n)} (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ∃ U : CanonicalMetricH1 d.potential,
      (canonicalMetricValue d.potential U : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
        (fun x => sourceTensorGramEntry d.potential T i j x -
          ∫ y, sourceTensorGramEntry d.potential T i j y ∂potentialMeasure d.potential) ∧
      ∀ r, (canonicalMetricGradient d.potential r U : Space n → ℝ)
        =ᵐ[potentialMeasure d.potential]
          rawCanonicalMetricDerivative d.potential
            (sourceTensorGramRawDerivative d.potential d.third T i j) r := by
  let g : Matrix (Fin n) (Fin n) ℝ → ℝ := fun A => (T i * A * T j * A).trace
  have hg : Continuous g := by fun_prop
  have hge : sourceTensorGramEntry d.potential T i j = fun x => g (coordinateHessian d.potential x) :=
    funext (sourceTensorGramEntry_eq_trace d.potential T i j)
  obtain ⟨B, hB⟩ := d.hessian_range_bounded.isCompact_closure.bddAbove_image hg.norm.continuousOn
  have hbound (x : Space n) : ‖sourceTensorGramEntry d.potential T i j x‖ ≤ B := by
    rw [hge]
    exact hB ⟨coordinateHessian d.potential x, subset_closure ⟨x, rfl⟩, rfl⟩
  have hm : AEStronglyMeasurable (sourceTensorGramEntry d.potential T i j)
      (potentialMeasure d.potential) := by
    rw [hge]
    exact (hg.measurable.comp (measurable_coordinateHessian d.potential)).aestronglyMeasurable
  exact d.bounded_raw_metric_pair_mem hm hbound
    (fun k E hE => d.tensorGram_derivative_local_L2 T i j k E hE)
    (fun k => d.tensorGram_hasLocalWeakCoordinateDerivative T i j k)
    (d.tensorGram_raw_energy_integrable T i j)

end KLSConstantImprovement.ActualSourceTensorGramMetricBinding
#print axioms KLSConstantImprovement.ActualSourceTensorGramMetricBinding.sourceTensorGramEntry_eq_trace
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.tensorGram_derivative_local_L2
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.tensorGram_hasLocalWeakCoordinateDerivative
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.tensorGram_raw_metric_memLp
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.tensorGram_raw_energy_integrable
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.hessian_range_bounded
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.exists_tensorGram_entry_metricH1

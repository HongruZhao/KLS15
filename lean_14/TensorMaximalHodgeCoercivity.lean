import TensorConstrainedHodgeCoercivity

/-! Coercivity on the literal full maximal weighted distributional Hodge
domain. Compact approximation is proved by the existing matrix graph core;
no core-density premise is introduced. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n r : ℕ} {φ : Space n → ℝ}

lemma finiteMatrixLp_norm_sq {ι : Type*} [Fintype ι]
    {μ : Measure (Space n)} (f : ι → Space n → ℝ) (hf : ∀ i, MemLp (f i) 2 μ) :
    ‖finiteMatrixLp f hf‖ ^ 2 = ∑ i, ∫ x, (f i x) ^ 2 ∂μ := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i _
  change ‖(hf i).toLp (f i)‖ ^ 2 = _
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hf i).coeFn_toLp] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial, pow_two]

lemma finiteMatrixLp_tensorTwoForm_norm_sq
    {f : TensorTwoFormIndex n (r + 1) → Space n → ℝ}
    (hf : ∀ z, MemLp (f z) 2 (potentialMeasure φ)) :
    ‖finiteMatrixLp f hf‖ ^ 2 =
      ∫ x, tensorTwoFormNormSq (fun z => f z x) ∂potentialMeasure φ := by
  rw [finiteMatrixLp_norm_sq]
  unfold tensorTwoFormNormSq
  have hsq (z : TensorTwoFormIndex n (r + 1)) :
      Integrable (fun x => (f z x) ^ 2) (potentialMeasure φ) := by
    simpa only [Real.norm_eq_abs, sq_abs] using (hf z).integrable_norm_pow (by norm_num : 2 ≠ 0)
  simp only [Fintype.sum_prod_type]
  symm
  rw [integral_finsetSum Finset.univ (fun I _ => integrable_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hsq (I, i, j))))]
  apply Finset.sum_congr rfl
  intro I _
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hsq (I, i, j)))]
  exact Finset.sum_congr rfl (fun i _ => integral_finsetSum Finset.univ (fun j _ => hsq (I, i, j)))

lemma tensorHodgeFirstOrderLp_norm_sq_eq
    (hφ : ContDiff ℝ 2 φ) {f : TensorTwoFormIndex n (r + 1) → Space n → ℝ}
    (hf : ∀ z, ContDiff ℝ 2 (f z)) (hc : ∀ z, HasCompactSupport (f z))
    (hg : ∀ a, MemLp (matrixFirstOrder (tensorHodgeDerivativeMatrix n (r + 1))
      (tensorHodgeDriftMatrix φ (r + 1)) f a) 2 (potentialMeasure φ)) :
    ‖finiteMatrixLp (matrixFirstOrder (tensorHodgeDerivativeMatrix n (r + 1))
      (tensorHodgeDriftMatrix φ (r + 1)) f) hg‖ ^ 2 = tensorConstrainedHodgeEnergy φ f := by
  rw [finiteMatrixLp_norm_sq, Fintype.sum_sum_type]
  unfold tensorConstrainedHodgeEnergy tensorTwoFormCurlEnergy
  congr 1
  · simp only [Fintype.sum_prod_type]
    simp_rw [tensorHodge_firstOrder_curl, mul_pow, _root_.one_div_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), integral_const_mul]
    simp only [twoFormCurlEnergy, Finset.mul_sum]
  · simp_rw [tensorHodge_firstOrder_projectedAdjoint]
    symm
    exact integral_euclidean_norm_sq (fun a => compact_coefficient_square_integrable hφ.continuous
      (tensorProjectedAdjoint_coefficient_continuous hφ hf a)
      (tensorProjectedAdjoint_coefficient_compact hc a))

/-- Actual compact distributional-matrix coercivity with the physical
rank constant. The Hessian lower bound is the only curvature input. -/
theorem compact_tensorHodge_norm_coercive
    (hφ : ContDiff ℝ 2 φ) {f : TensorTwoFormIndex n (r + 1) → Space n → ℝ}
    (hf : ∀ z, ContDiff ℝ 2 (f z)) (hc : ∀ z, HasCompactSupport (f z))
    (hF : ∀ x, TensorTwoFormCompatible (fun z => f z x))
    (hflp : ∀ z, MemLp (f z) 2 (potentialMeasure φ))
    (hglp : ∀ a, MemLp (matrixFirstOrder (tensorHodgeDerivativeMatrix n (r + 1))
      (tensorHodgeDriftMatrix φ (r + 1)) f a) 2 (potentialMeasure φ))
    {a : ℝ} (hlower : ∀ (x : Space n) (v : Fin n → ℝ),
      a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ x *ᵥ v)) :
    ((r + 3 : ℕ) / (r + 2 : ℕ) : ℝ) * a * ‖finiteMatrixLp f hflp‖ ^ 2 ≤
      ‖finiteMatrixLp (matrixFirstOrder (tensorHodgeDerivativeMatrix n (r + 1))
        (tensorHodgeDriftMatrix φ (r + 1)) f) hglp‖ ^ 2 := by
  rw [finiteMatrixLp_tensorTwoForm_norm_sq, tensorHodgeFirstOrderLp_norm_sq_eq hφ hf hc]
  have hb := tensorConstrainedHodgeEnergy_coercive hφ hf hc hF hlower
  have hn : 0 ≤ tensorTwoFormGradientEnergy φ f :=
    Finset.sum_nonneg fun I _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _
  have hcst : (0 : ℝ) ≤ 1 / (r + 2 : ℕ) := by positivity
  linarith [mul_nonneg hcst hn]

lemma norm_coercive_of_mem_closure {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {S : Set (E × F)} {p : E × F} {c : ℝ}
    (hp : p ∈ closure S) (hS : ∀ q ∈ S, c * ‖q.1‖ ^ 2 ≤ ‖q.2‖ ^ 2) :
    c * ‖p.1‖ ^ 2 ≤ ‖p.2‖ ^ 2 := by
  have hc : IsClosed {q : E × F | c * ‖q.1‖ ^ 2 ≤ ‖q.2‖ ^ 2} :=
    isClosed_le (continuous_const.mul (continuous_fst.norm.pow 2)) (continuous_snd.norm.pow 2)
  exact (closure_minimal hS hc) hp

/-- Coercivity on the full actual weighted distributional domain, retaining
all finite tensor constraints. The compact graph-core theorem is used as
a proved approximation result, not assumed as a hypothesis. -/
theorem maximal_tensorHodge_norm_coercive
    (hφ : ContDiff ℝ 2 φ)
    {f : TensorTwoFormIndex n (r + 1) → Space n → ℝ}
    {g : TensorHodgeOutputIndex n (r + 1) → Space n → ℝ}
    (h : HasWeakConstrainedTensorHodge φ (r + 1) f g)
    (hf : ∀ z, MemLp (f z) 2 (potentialMeasure φ))
    (hg : ∀ a, MemLp (g a) 2 (potentialMeasure φ))
    {a : ℝ} (hlower : ∀ (x : Space n) (v : Fin n → ℝ),
      a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ x *ᵥ v)) :
    ((r + 3 : ℕ) / (r + 2 : ℕ) : ℝ) * a * ‖finiteMatrixLp f hf‖ ^ 2 ≤
      ‖finiteMatrixLp g hg‖ ^ 2 := by
  apply norm_coercive_of_mem_closure
    (constrained_tensorHodge_graph_core (hφ.of_le (by norm_num)) (r + 1) h hf hg)
  rintro p ⟨F, hF, hc, hC, hflp, hglp, rfl⟩
  have hcompat (x : Space n) : TensorTwoFormCompatible (fun z => F z x) := by
    refine ⟨?_, ?_, ?_⟩
    · intro I J hp i j
      have he := hC (Sum.inl (I, J, i, j)) x
      rw [tensorTwoFormConstraintMatrix_symmetry, if_pos hp] at he
      exact sub_eq_zero.mp he
    · intro I i j
      have he := hC (Sum.inr (Sum.inl (I, i, j))) x
      rw [tensorTwoFormConstraintMatrix_skew] at he
      exact eq_neg_of_add_eq_zero_left he
    · intro I i j k
      have he := hC (Sum.inr (Sum.inr (I, i, j, k))) x
      simpa only [tensorTwoFormConstraintMatrix_koszul] using he
  exact compact_tensorHodge_norm_coercive hφ (fun z => (hF z).of_le (by simp))
    hc hcompat hflp hglp hlower

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.compact_tensorHodge_norm_coercive
#print axioms KLS.DeterministicBridgeIntegration.maximal_tensorHodge_norm_coercive

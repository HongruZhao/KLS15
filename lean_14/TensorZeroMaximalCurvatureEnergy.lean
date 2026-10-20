import TensorMaximalCurvatureEnergy
import TensorZeroAuxiliaryFiber
import TensorRankZeroCurvatureCoupling

/-! The auxiliary-degree-zero curvature energy on the actual full weak
Hodge domain. The compact estimate is the ordinary weighted two-form
Bochner identity because the one-form fiber projection is the identity.
The passage to the maximal domain uses the actual compact graph core and
Fatou, without an upper Hessian bound. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff Topology BigOperators ENNReal RealInnerProductSpace
namespace KLS.DeterministicBridgeIntegration
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
variable {n : ℕ} {φ : Space n → ℝ}

def tensorZeroCurvatureFiberFunction (φ : Space n → ℝ)
    (x : Space n) (v : EuclideanSpace ℝ (TensorTwoFormIndex n 0)) : ℝ :=
  tensorTwoFormCurvatureZero (coordinateHessian φ x) (fun z => v z)

lemma tensorZeroCurvatureFiberFunction_continuous (x : Space n) :
    Continuous (tensorZeroCurvatureFiberFunction φ x) := by
  unfold tensorZeroCurvatureFiberFunction tensorTwoFormCurvatureZero
  fun_prop

lemma tensorZeroCurvatureFiberFunction_aestronglyMeasurable
    (hφ : ContDiff ℝ 2 φ)
    (F : FiniteScalarLp (TensorTwoFormIndex n 0) (potentialMeasure φ)) :
    AEStronglyMeasurable
      (fun x => tensorZeroCurvatureFiberFunction φ x (finiteLpVectorFunction F x))
      (potentialMeasure φ) := by
  have hF (z : TensorTwoFormIndex n 0) :
      AEStronglyMeasurable (fun x => F z x) (potentialMeasure φ) := (Lp.memLp (F z)).aestronglyMeasurable
  have hK (i j : Fin n) : AEStronglyMeasurable (fun x => coordinateHessian φ x i j)
      (potentialMeasure φ) :=
    (contDiff_coordinateHessian hφ (m := 0) (by norm_num) i j).continuous.aestronglyMeasurable
  unfold tensorZeroCurvatureFiberFunction finiteLpVectorFunction tensorTwoFormCurvatureZero
  simp only [PiLp.toLp_apply]
  fun_prop

lemma tensorTwoFormCurvatureZero_nonneg {K : Matrix (Fin n) (Fin n) ℝ}
    (f : TensorTwoFormIndex n 0 → ℝ)
    (hK : ∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ (K *ᵥ v)) :
    0 ≤ tensorTwoFormCurvatureZero K f := by
  unfold tensorTwoFormCurvatureZero
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
  apply Finset.sum_nonneg
  intro I _
  rw [← finite_triple_sum_last_to_first]
  apply Finset.sum_nonneg
  intro k _
  have ht := hK (fun i => f (I,i,k))
  simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using ht

lemma integrable_tensorTwoFormCurvatureZero
    (hφ : ContDiff ℝ 2 φ) {f : TensorTwoFormIndex n 0 → Space n → ℝ}
    (hf : ∀ z, Continuous (f z)) (hc : ∀ z, HasCompactSupport (f z)) :
    Integrable (fun x => tensorTwoFormCurvatureZero (coordinateHessian φ x) (fun z => f z x))
      (potentialMeasure φ) := by
  unfold tensorTwoFormCurvatureZero
  apply Integrable.const_mul
  apply integrable_finsetSum Finset.univ
  intro I _
  apply integrable_finsetSum Finset.univ
  intro i _
  apply integrable_finsetSum Finset.univ
  intro j _
  apply integrable_finsetSum Finset.univ
  intro k _
  exact integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
    ((((contDiff_coordinateHessian hφ (m := 0) (by norm_num) i j).continuous).mul
      (hf _)).mul (hf _)) (hc _).mul_left.mul_right

lemma integral_tensorTwoFormCurvatureZero
    (hφ : ContDiff ℝ 2 φ) {f : TensorTwoFormIndex n 0 → Space n → ℝ}
    (hf : ∀ z, Continuous (f z)) (hc : ∀ z, HasCompactSupport (f z)) :
    (∫ x, tensorTwoFormCurvatureZero (coordinateHessian φ x) (fun z => f z x)
      ∂potentialMeasure φ) =
      ∑ I : OrderedTensorIndex n 0, twoFormCurvatureEnergy φ (fun i j => f (I,i,j)) := by
  have hint (I : OrderedTensorIndex n 0) (i j k : Fin n) :
      Integrable (fun x => coordinateHessian φ x i j * f (I,i,k) x * f (I,j,k) x)
        (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((((contDiff_coordinateHessian hφ (m := 0) (by norm_num) i j).continuous).mul
        (hf _)).mul (hf _)) (hc _).mul_left.mul_right
  unfold tensorTwoFormCurvatureZero
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun I _ =>
    integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
      (fun j _ => integrable_finsetSum Finset.univ (fun k _ => hint I i j k))))]
  simp_rw [integral_finite_triple_sum (hint _)]
  simp only [twoFormCurvatureEnergy, Finset.mul_sum]

lemma tensorHodgeZeroFirstOrderLp_norm_sq
    (hφ : ContDiff ℝ 2 φ) {f : TensorTwoFormIndex n 0 → Space n → ℝ}
    (hf : ∀ z, ContDiff ℝ 2 (f z)) (hc : ∀ z, HasCompactSupport (f z))
    (hg : ∀ a, MemLp (matrixFirstOrder (tensorHodgeDerivativeMatrix n 0)
      (tensorHodgeDriftMatrix φ 0) f a) 2 (potentialMeasure φ)) :
    ‖finiteMatrixLp (matrixFirstOrder (tensorHodgeDerivativeMatrix n 0)
      (tensorHodgeDriftMatrix φ 0) f) hg‖ ^ 2 =
      (∑ I : OrderedTensorIndex n 0, twoFormCurlEnergy φ (fun i j => f (I,i,j))) +
      ∑ I : OrderedTensorIndex n 0, twoFormAdjointEnergy φ (fun i j => f (I,i,j)) := by
  rw [finiteMatrixLp_norm_sq, Fintype.sum_sum_type]
  congr 1
  · simp only [Fintype.sum_prod_type]
    simp_rw [tensorHodge_firstOrder_curl, mul_pow, _root_.one_div_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), integral_const_mul]
    simp only [twoFormCurlEnergy, Finset.mul_sum]
  · simp_rw [tensorHodge_firstOrder_projectedAdjoint, tensorTwoFormWeightedAdjoint_zero_projection]
    simp only [Fintype.sum_prod_type, tensorTwoFormWeightedAdjoint, PiLp.toLp_apply,
      mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have he (I : OrderedTensorIndex n 0) (j : Fin n) (x : Space n) :
        (∑ i : Fin n, (-coordinateDerivative (f (I,i,j)) i x +
          coordinateDerivative φ i x * f (I,i,j) x)) =
        -(weightedVectorDivergence φ (fun i => f (I,i,j)) x) := by
      unfold weightedVectorDivergence weightedDerivativeTest
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp_rw [he, neg_sq, integral_const_mul]
    simp only [twoFormAdjointEnergy, Finset.mul_sum]

lemma compact_tensorHodgeZero_curvature_le
    (hφ : ContDiff ℝ 2 φ) {f : TensorTwoFormIndex n 0 → Space n → ℝ}
    (hf : ∀ z, ContDiff ℝ 2 (f z)) (hc : ∀ z, HasCompactSupport (f z))
    (hs : ∀ I i j, f (I,i,j) = -f (I,j,i))
    (hg : ∀ a, MemLp (matrixFirstOrder (tensorHodgeDerivativeMatrix n 0)
      (tensorHodgeDriftMatrix φ 0) f a) 2 (potentialMeasure φ)) :
    (∫ x, tensorTwoFormCurvatureZero (coordinateHessian φ x) (fun z => f z x)
      ∂potentialMeasure φ) ≤
      ‖finiteMatrixLp (matrixFirstOrder (tensorHodgeDerivativeMatrix n 0)
        (tensorHodgeDriftMatrix φ 0) f) hg‖ ^ 2 := by
  rw [integral_tensorTwoFormCurvatureZero hφ (fun z => (hf z).continuous) hc,
    tensorHodgeZeroFirstOrderLp_norm_sq hφ hf hc, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro I _
  rw [integral_weightedTwoFormHodge_core hφ (fun i j => hf _) (fun i j => hc _) (hs I)]
  have hn : 0 ≤ twoFormGradientEnergy φ (fun i j => f (I,i,j)) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
      integral_nonneg fun x => sq_nonneg _
  linarith

/-- The zero-auxiliary physical Q bound on the genuine maximal domain. -/
theorem maximal_tensorHodgeZero_curvature_lintegral_le
    (hφ : ContDiff ℝ 2 φ)
    {f : TensorTwoFormIndex n 0 → Space n → ℝ}
    {g : TensorHodgeOutputIndex n 0 → Space n → ℝ}
    (h : HasWeakConstrainedTensorHodge φ 0 f g)
    (hf : ∀ z, MemLp (f z) 2 (potentialMeasure φ))
    (hg : ∀ a, MemLp (g a) 2 (potentialMeasure φ))
    {a : ℝ} (ha : 0 ≤ a)
    (hlower : ∀ (x : Space n) (v : Fin n → ℝ),
      a*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ x *ᵥ v)) :
    (∫⁻ x, ENNReal.ofReal (tensorTwoFormCurvatureZero (coordinateHessian φ x)
      (fun z => f z x)) ∂potentialMeasure φ) ≤ ENNReal.ofReal (‖finiteMatrixLp g hg‖^2) := by
  have hnonneg (x : Space n) (F : TensorTwoFormIndex n 0 → ℝ) :
      0 ≤ tensorTwoFormCurvatureZero (coordinateHessian φ x) F :=
    tensorTwoFormCurvatureZero_nonneg F (fun v =>
      le_trans (mul_nonneg ha (by
        unfold dotProduct
        exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i)))) (hlower x v))
  have hb := finiteFiberEnergy_lintegral_le_of_graph_closure
    (tensorZeroCurvatureFiberFunction φ) (fun x => tensorZeroCurvatureFiberFunction_continuous x)
    (fun F => (tensorZeroCurvatureFiberFunction_aestronglyMeasurable hφ F).aemeasurable.ennreal_ofReal)
    (constrained_tensorHodge_graph_core (hφ.of_le (by norm_num)) 0 h hf hg) ?_
  · convert hb using 1
    apply lintegral_congr_ae
    filter_upwards [finiteMatrixLp_ae_coordinates f hf] with x hx
    simp only [tensorZeroCurvatureFiberFunction,finiteLpVectorFunction,PiLp.toLp_apply,hx]
  · rintro p ⟨F,hF,hc,hC,hflp,hglp,rfl⟩
    have hcompat (x : Space n) : TensorTwoFormCompatible (fun z => F z x) :=
      (mem_tensorTwoFormFiber_iff_compatible (WithLp.toLp 2 (fun z => F z x))).mp
        ((mem_tensorTwoFormFiber_iff _).mpr (fun z => hC z x))
    have hskew (I : OrderedTensorIndex n 0) (i j : Fin n) : F (I,i,j) = -F (I,j,i) :=
      funext fun x => (hcompat x).2.1 I i j
    have hint := integrable_tensorTwoFormCurvatureZero hφ (fun z => (hF z).continuous) hc
    have hQ := compact_tensorHodgeZero_curvature_le hφ (fun z => (hF z).of_le (by simp)) hc hskew hglp
    have hl : (∫⁻ x, ENNReal.ofReal (tensorZeroCurvatureFiberFunction φ x
        (finiteLpVectorFunction (finiteMatrixLp F hflp) x)) ∂potentialMeasure φ) =
        ENNReal.ofReal (∫ x, tensorTwoFormCurvatureZero (coordinateHessian φ x)
          (fun z => F z x) ∂potentialMeasure φ) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall (fun x => hnonneg x _))]
      apply lintegral_congr_ae
      filter_upwards [finiteMatrixLp_ae_coordinates F hflp] with x hx
      simp only [tensorZeroCurvatureFiberFunction,finiteLpVectorFunction,PiLp.toLp_apply,hx]
    rw [hl]
    exact ENNReal.ofReal_le_ofReal hQ

/-- Genuine integrability and the real-integral maximal-domain bound. -/
theorem maximal_tensorHodgeZero_curvature_integrable_le
    (hφ : ContDiff ℝ 2 φ)
    {f : TensorTwoFormIndex n 0 → Space n → ℝ}
    {g : TensorHodgeOutputIndex n 0 → Space n → ℝ}
    (h : HasWeakConstrainedTensorHodge φ 0 f g)
    (hf : ∀ z, MemLp (f z) 2 (potentialMeasure φ))
    (hg : ∀ z, MemLp (g z) 2 (potentialMeasure φ))
    {a : ℝ} (ha : 0 ≤ a)
    (hlower : ∀ (x : Space n) (v : Fin n → ℝ),
      a*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ x *ᵥ v)) :
    Integrable (fun x => tensorTwoFormCurvatureZero (coordinateHessian φ x)
      (fun z => f z x)) (potentialMeasure φ) ∧
    (∫ x, tensorTwoFormCurvatureZero (coordinateHessian φ x)
      (fun z => f z x) ∂potentialMeasure φ) ≤ ‖finiteMatrixLp g hg‖^2 := by
  have he : (fun x => tensorZeroCurvatureFiberFunction φ x
      (finiteLpVectorFunction (finiteMatrixLp f hf) x)) =ᵐ[potentialMeasure φ]
      (fun x => tensorTwoFormCurvatureZero (coordinateHessian φ x) (fun z => f z x)) := by
    filter_upwards [finiteMatrixLp_ae_coordinates f hf] with x hx
    simp only [tensorZeroCurvatureFiberFunction,finiteLpVectorFunction,PiLp.toLp_apply,hx]
  have hm := (tensorZeroCurvatureFiberFunction_aestronglyMeasurable hφ (finiteMatrixLp f hf)).congr he
  have hnn : 0 ≤ᵐ[potentialMeasure φ] (fun x =>
      tensorTwoFormCurvatureZero (coordinateHessian φ x) (fun z => f z x)) := by
    apply Eventually.of_forall
    intro x
    exact tensorTwoFormCurvatureZero_nonneg _ (fun v =>
      le_trans (mul_nonneg ha (by
        unfold dotProduct
        exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i)))) (hlower x v))
  have hb := maximal_tensorHodgeZero_curvature_lintegral_le hφ h hf hg ha hlower
  have hint : Integrable (fun x => tensorTwoFormCurvatureZero (coordinateHessian φ x)
      (fun z => f z x)) (potentialMeasure φ) :=
    ⟨hm,(hasFiniteIntegral_iff_ofReal hnn).mpr (hb.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hint,?_⟩
  rw [←ofReal_integral_eq_lintegral_ofReal hint hnn] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp hb

end KLS.DeterministicBridgeIntegration
end
#print axioms KLS.DeterministicBridgeIntegration.compact_tensorHodgeZero_curvature_le
#print axioms KLS.DeterministicBridgeIntegration.maximal_tensorHodgeZero_curvature_integrable_le

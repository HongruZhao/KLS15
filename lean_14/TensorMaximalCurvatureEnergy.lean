import FiniteFiberEnergyFatou

/-! The actual integrated constrained curvature lower bound on the full
maximal distributional matrix domain, using the proved graph core and
Fatou. No Hessian upper bound or assumed energy continuity is needed. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff Topology BigOperators ENNReal RealInnerProductSpace
namespace KLS.DeterministicBridgeIntegration
open KLS
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {n r : ℕ} {φ : Space n → ℝ}

def tensorCurvatureFiberFunction (φ : Space n → ℝ) (r : ℕ)
    (x : Space n) (v : EuclideanSpace ℝ (TensorTwoFormIndex n (r+1))) : ℝ :=
  tensorTwoFormCurvatureCorrection (coordinateHessian φ x) (fun z => v z)

lemma tensorCurvatureFiberFunction_continuous (x : Space n) :
    Continuous (tensorCurvatureFiberFunction φ r x) := by
  unfold tensorCurvatureFiberFunction tensorTwoFormCurvatureCorrection
    tensorTwoFormExteriorCurvatureForm tensorTwoFormAuxiliaryCurvatureForm tensorAuxiliaryCurvatureForm
  fun_prop

lemma tensorCurvatureFiberFunction_aestronglyMeasurable
    (hφ : ContDiff ℝ 2 φ)
    (F : FiniteScalarLp (TensorTwoFormIndex n (r+1)) (potentialMeasure φ)) :
    AEStronglyMeasurable
      (fun x => tensorCurvatureFiberFunction φ r x (finiteLpVectorFunction F x))
      (potentialMeasure φ) := by
  have hF (z : TensorTwoFormIndex n (r+1)) :
      AEStronglyMeasurable (fun x => F z x) (potentialMeasure φ) := (Lp.memLp (F z)).aestronglyMeasurable
  have hK (i j : Fin n) : AEStronglyMeasurable (fun x => coordinateHessian φ x i j)
      (potentialMeasure φ) :=
    (contDiff_coordinateHessian hφ (m := 0) (by norm_num) i j).continuous.aestronglyMeasurable
  unfold tensorCurvatureFiberFunction finiteLpVectorFunction tensorTwoFormCurvatureCorrection
    tensorTwoFormExteriorCurvatureForm tensorTwoFormAuxiliaryCurvatureForm tensorAuxiliaryCurvatureForm
  simp only [PiLp.toLp_apply]
  fun_prop

lemma finiteMatrixLp_ae_coordinates {ι : Type*} [Fintype ι]
    {μ : Measure (Space n)} (f : ι → Space n → ℝ) (hf : ∀ i, MemLp (f i) 2 μ) :
    ∀ᵐ x ∂μ, ∀ i, finiteMatrixLp f hf i x=f i x :=
  ae_all_iff.mpr (fun i => (hf i).coeFn_toLp)

lemma weakConstrainedTensorHodge_compatible_ae
    {f : TensorTwoFormIndex n (r+1) → Space n → ℝ}
    {g : TensorHodgeOutputIndex n (r+1) → Space n → ℝ}
    (h : HasWeakConstrainedTensorHodge φ (r+1) f g) :
    ∀ᵐ x ∂potentialMeasure φ, TensorTwoFormCompatible (fun z => f z x) := by
  have hall : ∀ᵐ x ∂volume, ∀ a,
      (∑ z, tensorTwoFormConstraintMatrix n (r+1) a z*f z x)=0 :=
    ae_all_iff.mpr h.2
  have hw := (withDensity_absolutelyContinuous volume
    (fun x => ENNReal.ofReal (Real.exp (-φ x)))) hall
  filter_upwards [hw] with x hx
  apply (mem_tensorTwoFormFiber_iff_compatible (WithLp.toLp 2 (fun z => f z x))).mp
  exact (mem_tensorTwoFormFiber_iff _).mpr hx

/-- The literal constrained Q energy is bounded on the entire actual
joint weak matrix domain. -/
theorem maximal_tensorHodge_curvature_lintegral_le
    (hφ : ContDiff ℝ 2 φ)
    {f : TensorTwoFormIndex n (r+1) → Space n → ℝ}
    {g : TensorHodgeOutputIndex n (r+1) → Space n → ℝ}
    (h : HasWeakConstrainedTensorHodge φ (r+1) f g)
    (hf : ∀ z, MemLp (f z) 2 (potentialMeasure φ))
    (hg : ∀ a, MemLp (g a) 2 (potentialMeasure φ))
    {a : ℝ} (ha : 0 ≤ a)
    (hlower : ∀ (x : Space n) (v : Fin n → ℝ),
      a*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ x *ᵥ v)) :
    (∫⁻ x, ENNReal.ofReal (tensorTwoFormCurvatureCorrection (coordinateHessian φ x)
      (fun z => f z x)) ∂potentialMeasure φ) ≤ ENNReal.ofReal (‖finiteMatrixLp g hg‖^2) := by
  have hb := finiteFiberEnergy_lintegral_le_of_graph_closure
    (tensorCurvatureFiberFunction φ r) (fun x => tensorCurvatureFiberFunction_continuous x)
    (fun F => (tensorCurvatureFiberFunction_aestronglyMeasurable hφ F).aemeasurable.ennreal_ofReal)
    (constrained_tensorHodge_graph_core (hφ.of_le (by norm_num)) (r+1) h hf hg) ?_
  · convert hb using 1
    apply lintegral_congr_ae
    filter_upwards [finiteMatrixLp_ae_coordinates f hf] with x hx
    simp only [tensorCurvatureFiberFunction,finiteLpVectorFunction,PiLp.toLp_apply,hx]
  · rintro p ⟨F,hF,hc,hC,hflp,hglp,rfl⟩
    have hcompat (x : Space n) : TensorTwoFormCompatible (fun z => F z x) :=
      (mem_tensorTwoFormFiber_iff_compatible (WithLp.toLp 2 (fun z => F z x))).mp
        ((mem_tensorTwoFormFiber_iff _).mpr (fun z => hC z x))
    have hnn : ∀ x, 0 ≤ tensorTwoFormCurvatureCorrection (coordinateHessian φ x) (fun z => F z x) := by
      intro x
      have ht := tensorTwoFormCurvatureCorrection_lower _ (coordinateHessian_symmetric hφ x)
        (fun z => F z x) (hcompat x) (hlower x)
      exact le_trans (by unfold tensorTwoFormNormSq; positivity) ht
    have hint := (integrable_tensorTwoFormExteriorCurvatureForm hφ
      (fun z => (hF z).continuous) hc).sub
      ((integrable_tensorTwoFormAuxiliaryCurvatureForm hφ
        (fun z => (hF z).continuous) hc).const_mul (1/(r+2:ℕ)))
    change Integrable (fun x => tensorTwoFormCurvatureCorrection (coordinateHessian φ x)
      (fun z => F z x)) (potentialMeasure φ) at hint
    have hQ : (∫ x, tensorTwoFormCurvatureCorrection (coordinateHessian φ x)
        (fun z => F z x) ∂potentialMeasure φ) ≤
        ‖finiteMatrixLp (matrixFirstOrder (tensorHodgeDerivativeMatrix n (r+1))
          (tensorHodgeDriftMatrix φ (r+1)) F) hglp‖^2 := by
      rw [tensorHodgeFirstOrderLp_norm_sq_eq hφ (fun z => (hF z).of_le (by simp)) hc]
      have ht := tensorConstrainedHodgeEnergy_lower_gradient_curvature hφ
        (fun z => (hF z).of_le (by simp)) hc hcompat
      have hn : 0 ≤ tensorTwoFormGradientEnergy φ F :=
        Finset.sum_nonneg fun I _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
          Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _
      linarith [mul_nonneg (by positivity : (0:ℝ)≤1/(r+2:ℕ)) hn]
    have hl : (∫⁻ x, ENNReal.ofReal (tensorCurvatureFiberFunction φ r x
        (finiteLpVectorFunction (finiteMatrixLp F hflp) x)) ∂potentialMeasure φ) =
        ENNReal.ofReal (∫ x, tensorTwoFormCurvatureCorrection (coordinateHessian φ x)
          (fun z => F z x) ∂potentialMeasure φ) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn)]
      apply lintegral_congr_ae
      filter_upwards [finiteMatrixLp_ae_coordinates F hflp] with x hx
      simp only [tensorCurvatureFiberFunction,finiteLpVectorFunction,PiLp.toLp_apply,hx]
    rw [hl]
    exact ENNReal.ofReal_le_ofReal hQ

/-- The full actual curvature energy is integrable, and the real integral
has the genuine maximal Hodge energy as an upper bound. -/
theorem maximal_tensorHodge_curvature_integrable_le
    (hφ : ContDiff ℝ 2 φ)
    {f : TensorTwoFormIndex n (r+1) → Space n → ℝ}
    {g : TensorHodgeOutputIndex n (r+1) → Space n → ℝ}
    (h : HasWeakConstrainedTensorHodge φ (r+1) f g)
    (hf : ∀ z, MemLp (f z) 2 (potentialMeasure φ))
    (hg : ∀ z, MemLp (g z) 2 (potentialMeasure φ))
    {a : ℝ} (ha : 0 ≤ a)
    (hlower : ∀ (x : Space n) (v : Fin n → ℝ),
      a*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ x *ᵥ v)) :
    Integrable (fun x => tensorTwoFormCurvatureCorrection (coordinateHessian φ x)
      (fun z => f z x)) (potentialMeasure φ) ∧
    (∫ x, tensorTwoFormCurvatureCorrection (coordinateHessian φ x)
      (fun z => f z x) ∂potentialMeasure φ) ≤ ‖finiteMatrixLp g hg‖^2 := by
  have he : (fun x => tensorCurvatureFiberFunction φ r x
      (finiteLpVectorFunction (finiteMatrixLp f hf) x)) =ᵐ[potentialMeasure φ]
      (fun x => tensorTwoFormCurvatureCorrection (coordinateHessian φ x) (fun z => f z x)) := by
    filter_upwards [finiteMatrixLp_ae_coordinates f hf] with x hx
    simp only [tensorCurvatureFiberFunction,finiteLpVectorFunction,PiLp.toLp_apply,hx]
  have hm := (tensorCurvatureFiberFunction_aestronglyMeasurable hφ (finiteMatrixLp f hf)).congr he
  have hnn : 0 ≤ᵐ[potentialMeasure φ] (fun x =>
      tensorTwoFormCurvatureCorrection (coordinateHessian φ x) (fun z => f z x)) := by
    filter_upwards [weakConstrainedTensorHodge_compatible_ae h] with x hx
    have ht := tensorTwoFormCurvatureCorrection_lower _ (coordinateHessian_symmetric hφ x)
      (fun z => f z x) hx (hlower x)
    exact le_trans (by unfold tensorTwoFormNormSq; positivity) ht
  have hb := maximal_tensorHodge_curvature_lintegral_le hφ h hf hg ha hlower
  have hint : Integrable (fun x => tensorTwoFormCurvatureCorrection (coordinateHessian φ x)
      (fun z => f z x)) (potentialMeasure φ) :=
    ⟨hm,(hasFiniteIntegral_iff_ofReal hnn).mpr (hb.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hint,?_⟩
  rw [←ofReal_integral_eq_lintegral_ofReal hint hnn] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp hb

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.maximal_tensorHodge_curvature_lintegral_le

#print axioms KLS.DeterministicBridgeIntegration.maximal_tensorHodge_curvature_integrable_le

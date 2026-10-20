import KLS.WeightedEnergyGraphCore
import KLS.WeightedSmoothVariance
import KLS.MatrixInverseSqrtLipschitz
import KLS.HessianMetricProduct
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
# The actual inverse-Hessian energy graph

This is the closed graph of centered compact C3 test functions and their
genuine inverse-square-root-Hessian gradients.  The ambient direct sum is
only a Hilbert space: its derivative coordinates are not the ordinary
`weightedH1Derivative`.  Brascamp--Lieb proves coercivity of this actual
metric graph; no coercivity or operator certificate is an input.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Set Filter Matrix
open scoped BigOperators ContDiff RealInnerProductSpace MatrixOrder Matrix.Norms.Elementwise

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLSConstantImprovement.ActualCanonicalMetricEnergyGraph

open KLS
variable {n : ℕ}

/-- The actual symmetric inverse positive square root of the source Hessian. -/
def canonicalMetricRoot (φ : Space n → ℝ) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ := inverseSqrtMatrix (coordinateHessian φ x)

theorem canonicalMetricRoot_gram {φ : Space n → ℝ}
    (hpos : ∀ x, (coordinateHessian φ x).PosDef) (x : Space n) :
    (canonicalMetricRoot φ x).transpose * canonicalMetricRoot φ x =
      (coordinateHessian φ x)⁻¹ := by
  unfold canonicalMetricRoot
  rw [(inverseSqrtMatrix_isSymm (coordinateHessian φ x)).eq]
  unfold inverseSqrtMatrix
  rw [← Matrix.mul_inv_rev,
    CFC.sqrt_mul_sqrt_self (coordinateHessian φ x) (hpos x).posSemidef.nonneg]

theorem canonicalMetricRoot_continuous {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hpos : ∀ x, (coordinateHessian φ x).PosDef) :
    Continuous (canonicalMetricRoot φ) := by
  have hH : LocallyLipschitz (coordinateHessian φ) :=
    ((contDiff_coordinateHessian_matrix hφ).of_le
      (by norm_num : (1 : ℕ∞ω) ≤ 2)).locallyLipschitz
  exact (locallyLipschitz_inverseSqrtMatrix_comp hH hpos).continuous

/-- The actual metric gradient coordinate of a test. -/
def canonicalMetricDerivative (φ f : Space n → ℝ) (i : Fin n) (x : Space n) : ℝ :=
  ∑ j, canonicalMetricRoot φ x i j * coordinateDerivative f j x

theorem canonicalMetricDerivative_pair {φ : Space n → ℝ}
    (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (f g : Space n → ℝ) (x : Space n) :
    (∑ i, canonicalMetricDerivative φ f i x * canonicalMetricDerivative φ g i x) =
      hessianMetricGradientPair φ f g x := by
  let R := canonicalMetricRoot φ x
  let a : Fin n → ℝ := fun i => coordinateDerivative f i x
  let b : Fin n → ℝ := fun i => coordinateDerivative g i x
  have he : (R *ᵥ a) ⬝ᵥ (R *ᵥ b) = a ⬝ᵥ ((coordinateHessian φ x)⁻¹ *ᵥ b) := by
    rw [dotProduct_comm (R *ᵥ a) (R *ᵥ b),
      ← Matrix.dotProduct_transpose_mulVec R a (R *ᵥ b),
      Matrix.mulVec_mulVec, canonicalMetricRoot_gram hpos x]
  change (R *ᵥ a) ⬝ᵥ (R *ᵥ b) = _
  rw [he]
  unfold hessianMetricGradientPair
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp [a, b]
  ring

theorem canonicalMetricDerivative_sq {φ : Space n → ℝ}
    (hpos : ∀ x, (coordinateHessian φ x).PosDef) (f : Space n → ℝ) (x : Space n) :
    (∑ i, canonicalMetricDerivative φ f i x ^ 2) = inverseHessianGradientForm φ f x := by
  simpa only [pow_two, hessianMetricGradientPair, inverseHessianGradientForm] using
    canonicalMetricDerivative_pair hpos f f x

theorem canonicalMetricDerivative_continuous {φ f : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hf : ContDiff ℝ 1 f) (i : Fin n) :
    Continuous (canonicalMetricDerivative φ f i) := by
  unfold canonicalMetricDerivative
  apply continuous_finsetSum
  intro j _
  exact ((continuous_apply j).comp ((continuous_apply i).comp
    (canonicalMetricRoot_continuous hφ hpos))).mul
      (contDiff_coordinateDerivative hf (m := 0) (by norm_num) j).continuous

theorem canonicalMetricDerivative_hasCompactSupport {φ f : Space n → ℝ}
    (hc : HasCompactSupport f) (i : Fin n) :
    HasCompactSupport (canonicalMetricDerivative φ f i) := by
  unfold canonicalMetricDerivative
  have hs : (fun x => ∑ j, canonicalMetricRoot φ x i j * coordinateDerivative f j x) =
      ∑ j : Fin n, fun x => canonicalMetricRoot φ x i j * coordinateDerivative f j x := by
    funext x
    simp only [Finset.sum_apply]
  rw [hs]
  exact HasCompactSupport.finset_sum (s := Finset.univ) fun j _ =>
    (hasCompactSupport_coordinateDerivative hc j).mul_left

theorem canonicalMetricDerivative_memLp {φ f : Space n → ℝ}
    (hφ : ContDiff ℝ 4 φ) (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (i : Fin n) :
    MemLp (canonicalMetricDerivative φ f i) 2 (potentialMeasure φ) :=
  memLp_of_continuous_hasCompactSupport hφ.continuous
    (canonicalMetricDerivative_continuous hφ hpos hf i)
    (canonicalMetricDerivative_hasCompactSupport hc i)

theorem canonicalMetricDerivative_add {φ f g : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (i : Fin n) (x : Space n) :
    canonicalMetricDerivative φ (f + g) i x =
      canonicalMetricDerivative φ f i x + canonicalMetricDerivative φ g i x := by
  unfold canonicalMetricDerivative
  simp_rw [coordinateDerivative_add (hf.differentiable (by norm_num) x)
    (hg.differentiable (by norm_num) x), mul_add, Finset.sum_add_distrib]

theorem canonicalMetricDerivative_smul {φ f : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (c : ℝ) (i : Fin n) (x : Space n) :
    canonicalMetricDerivative φ (c • f) i x = c * canonicalMetricDerivative φ f i x := by
  unfold canonicalMetricDerivative
  simp_rw [coordinateDerivative_smul (hf.differentiable (by norm_num) x),
    mul_left_comm _ c, ← Finset.mul_sum]

/-- Genuine compact tests, with actual centering and actual metric derivatives. -/
def smoothCanonicalMetricGraphSet (φ : Space n → ℝ) : Set (WeightedEnergyAmbient φ) :=
  {U | ∃ f : Space n → ℝ, ContDiff ℝ 3 f ∧ HasCompactSupport f ∧
    ((U 0 : Lp ℝ 2 (potentialMeasure φ)) : Space n → ℝ) =ᵐ[potentialMeasure φ]
      (fun x => f x - ∫ y, f y ∂potentialMeasure φ) ∧
    ∀ i : Fin n,
      ((U i.succ : Lp ℝ 2 (potentialMeasure φ)) : Space n → ℝ) =ᵐ[potentialMeasure φ]
        canonicalMetricDerivative φ f i}

def canonicalMetricGraph (φ : Space n → ℝ) : Submodule ℝ (WeightedEnergyAmbient φ) :=
  (Submodule.span ℝ (smoothCanonicalMetricGraphSet φ)).topologicalClosure

abbrev CanonicalMetricH1 (φ : Space n → ℝ) := ↥(canonicalMetricGraph φ)

instance canonicalMetricH1_completeSpace (φ : Space n → ℝ) :
    CompleteSpace (CanonicalMetricH1 φ) := by
  unfold CanonicalMetricH1 canonicalMetricGraph
  infer_instance

def canonicalMetricValue (φ : Space n → ℝ) :
    CanonicalMetricH1 φ →L[ℝ] Lp ℝ 2 (potentialMeasure φ) :=
  (PiLp.proj 2 (fun _ : Fin (n + 1) => Lp ℝ 2 (potentialMeasure φ)) 0).comp
    (canonicalMetricGraph φ).subtypeL

def canonicalMetricGradient (φ : Space n → ℝ) (i : Fin n) :
    CanonicalMetricH1 φ →L[ℝ] Lp ℝ 2 (potentialMeasure φ) :=
  (PiLp.proj 2 (fun _ : Fin (n + 1) => Lp ℝ 2 (potentialMeasure φ)) i.succ).comp
    (canonicalMetricGraph φ).subtypeL

@[simp] theorem canonicalMetricValue_apply (φ : Space n → ℝ) (U : CanonicalMetricH1 φ) :
    canonicalMetricValue φ U = (U : WeightedEnergyAmbient φ) 0 := rfl

@[simp] theorem canonicalMetricGradient_apply (φ : Space n → ℝ)
    (U : CanonicalMetricH1 φ) (i : Fin n) :
    canonicalMetricGradient φ i U = (U : WeightedEnergyAmbient φ) i.succ := rfl

theorem canonicalMetricH1_norm_sq (φ : Space n → ℝ) (U : CanonicalMetricH1 φ) :
    ‖U‖ ^ 2 = ‖canonicalMetricValue φ U‖ ^ 2 +
      ∑ i : Fin n, ‖canonicalMetricGradient φ i U‖ ^ 2 := by
  change ‖(U : WeightedEnergyAmbient φ)‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
  rfl

private theorem core_zero (φ : Space n → ℝ) :
    (0 : WeightedEnergyAmbient φ) ∈ smoothCanonicalMetricGraphSet φ := by
  refine ⟨0, contDiff_const, HasCompactSupport.zero, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_zero ℝ 2 (potentialMeasure φ)] with x hx
    change (0 : Lp ℝ 2 (potentialMeasure φ)) x = _
    rw [hx]
    simp
  · intro i
    filter_upwards [Lp.coeFn_zero ℝ 2 (potentialMeasure φ)] with x hx
    change (0 : Lp ℝ 2 (potentialMeasure φ)) x = _
    rw [hx]
    simp [canonicalMetricDerivative, coordinateDerivative]

private theorem core_add {φ : Space n → ℝ} (hφ : Continuous φ)
    {U V : WeightedEnergyAmbient φ}
    (hU : U ∈ smoothCanonicalMetricGraphSet φ) (hV : V ∈ smoothCanonicalMetricGraphSet φ) :
    U + V ∈ smoothCanonicalMetricGraphSet φ := by
  obtain ⟨f, hf, hfc, hu, hud⟩ := hU
  obtain ⟨g, hg, hgc, hv, hvd⟩ := hV
  have hfI := integrable_potentialMeasure_of_continuous_hasCompactSupport hφ hf.continuous hfc
  have hgI := integrable_potentialMeasure_of_continuous_hasCompactSupport hφ hg.continuous hgc
  refine ⟨f + g, hf.add hg, hfc.add hgc, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_add (U 0) (V 0), hu, hv] with x hx hux hvx
    change (U 0 + V 0) x = _
    rw [hx]
    simp only [Pi.add_apply]
    rw [hux, hvx, integral_add hfI hgI]
    ring
  · intro i
    filter_upwards [Lp.coeFn_add (U i.succ) (V i.succ), hud i, hvd i] with x hx hux hvx
    change (U i.succ + V i.succ) x = _
    rw [hx]
    simp only [Pi.add_apply]
    rw [hux, hvx, canonicalMetricDerivative_add
      (hf.of_le (by norm_num)) (hg.of_le (by norm_num))]

private theorem core_smul {φ : Space n → ℝ}
    {U : WeightedEnergyAmbient φ} (c : ℝ) (hU : U ∈ smoothCanonicalMetricGraphSet φ) :
    c • U ∈ smoothCanonicalMetricGraphSet φ := by
  obtain ⟨f, hf, hfc, hu, hud⟩ := hU
  refine ⟨c • f, hf.const_smul c, hfc.smul_left, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_smul c (U 0), hu] with x hx hux
    change (c • U 0) x = _
    rw [hx]
    simp only [Pi.smul_apply]
    rw [hux, integral_smul]
    simp only [smul_eq_mul]
    ring
  · intro i
    filter_upwards [Lp.coeFn_smul c (U i.succ), hud i] with x hx hux
    change (c • U i.succ) x = _
    rw [hx]
    simp only [Pi.smul_apply]
    rw [hux, canonicalMetricDerivative_smul (hf.of_le (by norm_num))]
    rfl

def smoothCanonicalMetricCore {φ : Space n → ℝ} (hφ : Continuous φ) :
    Submodule ℝ (WeightedEnergyAmbient φ) where
  carrier := smoothCanonicalMetricGraphSet φ
  zero_mem' := core_zero φ
  add_mem' := core_add hφ
  smul_mem' := fun c _ hU => core_smul c hU

theorem canonicalMetricGraph_coe_eq_closure {φ : Space n → ℝ} (hφ : Continuous φ) :
    (canonicalMetricGraph φ : Set (WeightedEnergyAmbient φ)) =
      closure (smoothCanonicalMetricGraphSet φ) := by
  have hs : Submodule.span ℝ (smoothCanonicalMetricGraphSet φ) =
      smoothCanonicalMetricCore hφ := by
    change Submodule.span ℝ (smoothCanonicalMetricCore hφ : Set (WeightedEnergyAmbient φ)) = _
    exact Submodule.span_eq _
  rw [canonicalMetricGraph, hs]
  rfl

theorem exists_canonicalMetricH1_of_smoothCompact {φ f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 4 φ) (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (hf : ContDiff ℝ 3 f) (hc : HasCompactSupport f) :
    ∃ U : CanonicalMetricH1 φ,
      ((canonicalMetricValue φ U : Lp ℝ 2 (potentialMeasure φ)) : Space n → ℝ)
        =ᵐ[potentialMeasure φ] (fun x => f x - ∫ y, f y ∂potentialMeasure φ) ∧
      ∀ i : Fin n,
        ((canonicalMetricGradient φ i U : Lp ℝ 2 (potentialMeasure φ)) : Space n → ℝ)
          =ᵐ[potentialMeasure φ] canonicalMetricDerivative φ f i := by
  let hf2 := memLp_of_continuous_hasCompactSupport hφ.continuous hf.continuous hc
  let hd2 (i : Fin n) := canonicalMetricDerivative_memLp hφ hpos (hf.of_le (by norm_num)) hc i
  let F : Lp ℝ 2 (potentialMeasure φ) := hf2.toLp f
  let G (i : Fin n) : Lp ℝ 2 (potentialMeasure φ) :=
    (hd2 i).toLp (canonicalMetricDerivative φ f i)
  let W : WeightedEnergyAmbient φ :=
    WithLp.toLp 2 (Fin.cases (CenteredL2.center (potentialMeasure φ) F) G)
  have hW0 : ((W 0 : Lp ℝ 2 (potentialMeasure φ)) : Space n → ℝ)
      =ᵐ[potentialMeasure φ] (fun x => f x - ∫ y, f y ∂potentialMeasure φ) := by
    have hF : (F : Space n → ℝ) =ᵐ[potentialMeasure φ] f := hf2.coeFn_toLp
    have hi : (∫ x, F x ∂potentialMeasure φ) = ∫ x, f x ∂potentialMeasure φ := integral_congr_ae hF
    filter_upwards [CenteredL2.center_ae (potentialMeasure φ) F, hF] with x hx hy
    change (CenteredL2.center (potentialMeasure φ) F) x = _
    rw [hx, hi, hy]
  have hWi (i : Fin n) : ((W i.succ : Lp ℝ 2 (potentialMeasure φ)) : Space n → ℝ)
      =ᵐ[potentialMeasure φ] canonicalMetricDerivative φ f i := (hd2 i).coeFn_toLp
  have hW : W ∈ canonicalMetricGraph φ :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, hf, hc, hW0, hWi⟩)
  exact ⟨⟨W, hW⟩, hW0, hWi⟩

theorem canonicalMetricValue_integral_eq_zero {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hφ : Continuous φ)
    (U : CanonicalMetricH1 φ) :
    (∫ x, canonicalMetricValue φ U x ∂potentialMeasure φ) = 0 := by
  let M : WeightedEnergyAmbient φ →L[ℝ] ℝ :=
    (innerSL ℝ (CenteredL2.oneLp (potentialMeasure φ))).comp
      (PiLp.proj 2 (fun _ : Fin (n + 1) => Lp ℝ 2 (potentialMeasure φ)) 0)
  have hM (W : WeightedEnergyAmbient φ) : M W = ∫ x, W 0 x ∂potentialMeasure φ :=
    CenteredL2.inner_oneLp (potentialMeasure φ) (W 0)
  have hs : smoothCanonicalMetricGraphSet φ ⊆ LinearMap.ker M.toLinearMap := by
    rintro W ⟨f, hf, hc, hW, -⟩
    change M W = 0
    rw [hM, integral_congr_ae hW]
    have hfI := integrable_potentialMeasure_of_continuous_hasCompactSupport hφ hf.continuous hc
    rw [integral_sub hfI (integrable_const _)]
    simp
  have hcl := Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr hs) M.isClosed_ker
  have hU := hcl U.property
  change M (U : WeightedEnergyAmbient φ) = 0 at hU
  rw [hM] at hU
  exact hU

private theorem core_value_norm_sq_le {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 4 φ) (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    {U : WeightedEnergyAmbient φ} (hU : U ∈ smoothCanonicalMetricGraphSet φ) :
    ‖U 0‖ ^ 2 ≤ ∑ i : Fin n, ‖U i.succ‖ ^ 2 := by
  obtain ⟨f, hf, hc, hv, hd⟩ := hU
  have hvnorm : ‖U 0‖ ^ 2 = ProbabilityTheory.variance f (potentialMeasure φ) := by
    rw [ProbabilityTheory.variance_eq_integral hf.continuous.aemeasurable,
      ← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    simp [hx, pow_two]
  have hd2 (i : Fin n) := canonicalMetricDerivative_memLp hφ hpos (hf.of_le (by norm_num)) hc i
  have hdnorm (i : Fin n) : ‖U i.succ‖ ^ 2 =
      ∫ x, canonicalMetricDerivative φ f i x ^ 2 ∂potentialMeasure φ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hd i] with x hx
    simp [hx, pow_two]
  rw [hvnorm]
  simp_rw [hdnorm]
  rw [← integral_finsetSum Finset.univ (fun i _ => (hd2 i).integrable_sq)]
  have heq : (fun x => ∑ i, canonicalMetricDerivative φ f i x ^ 2) =
      inverseHessianGradientForm φ f := funext (canonicalMetricDerivative_sq hpos f)
  rw [heq]
  exact brascampLieb_variance_smooth_compact (hφ.of_le (by norm_num))
    (hf.of_le (by norm_num)) hpos hc

/-- BL passes through the actual metric graph closure. -/
theorem canonicalMetricValue_norm_sq_le_energy {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 4 φ) (hpos : ∀ x, (coordinateHessian φ x).PosDef)
    (U : CanonicalMetricH1 φ) :
    ‖canonicalMetricValue φ U‖ ^ 2 ≤ ∑ i : Fin n, ‖canonicalMetricGradient φ i U‖ ^ 2 := by
  have hclosed : IsClosed {W : WeightedEnergyAmbient φ |
      ‖W 0‖ ^ 2 ≤ ∑ i : Fin n, ‖W i.succ‖ ^ 2} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hcore : smoothCanonicalMetricGraphSet φ ⊆ {W : WeightedEnergyAmbient φ |
      ‖W 0‖ ^ 2 ≤ ∑ i : Fin n, ‖W i.succ‖ ^ 2} :=
    fun _ hW => core_value_norm_sq_le hφ hpos hW
  have hU : (U : WeightedEnergyAmbient φ) ∈ closure (smoothCanonicalMetricGraphSet φ) := by
    rw [← canonicalMetricGraph_coe_eq_closure hφ.continuous]
    exact U.property
  exact (closure_minimal hcore hclosed) hU

def canonicalMetricEnergy (φ : Space n → ℝ) :
    CanonicalMetricH1 φ →L[ℝ] CanonicalMetricH1 φ →L[ℝ] ℝ :=
  ∑ i : Fin n, (innerSL ℝ).bilinearComp
    (canonicalMetricGradient φ i) (canonicalMetricGradient φ i)

@[simp] theorem canonicalMetricEnergy_apply (φ : Space n → ℝ) (U V : CanonicalMetricH1 φ) :
    canonicalMetricEnergy φ U V =
      ∑ i : Fin n, inner ℝ (canonicalMetricGradient φ i U) (canonicalMetricGradient φ i V) := by
  simp [canonicalMetricEnergy]

@[simp] theorem canonicalMetricEnergy_self (φ : Space n → ℝ) (U : CanonicalMetricH1 φ) :
    canonicalMetricEnergy φ U U = ∑ i : Fin n, ‖canonicalMetricGradient φ i U‖ ^ 2 := by
  simp [canonicalMetricEnergy_apply]

theorem canonicalMetricEnergy_symm (φ : Space n → ℝ) (U V : CanonicalMetricH1 φ) :
    canonicalMetricEnergy φ U V = canonicalMetricEnergy φ V U := by
  simp only [canonicalMetricEnergy_apply]
  exact Finset.sum_congr rfl (fun _ _ => real_inner_comm _ _)

/-- The actual source BL inequality supplies the fixed positive coercivity
constant; it is not an assumed metric spectral gap. -/
theorem canonicalMetricEnergy_isCoercive {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 4 φ) (hpos : ∀ x, (coordinateHessian φ x).PosDef) :
    IsCoercive (canonicalMetricEnergy φ) := by
  refine ⟨(1 / 2 : ℝ), by norm_num, fun U => ?_⟩
  have hP := canonicalMetricValue_norm_sq_le_energy hφ hpos U
  have hn := canonicalMetricH1_norm_sq φ U
  rw [canonicalMetricEnergy_self]
  nlinarith

end KLSConstantImprovement.ActualCanonicalMetricEnergyGraph
end

#print axioms KLSConstantImprovement.ActualCanonicalMetricEnergyGraph.canonicalMetricDerivative_pair
#print axioms KLSConstantImprovement.ActualCanonicalMetricEnergyGraph.exists_canonicalMetricH1_of_smoothCompact
#print axioms KLSConstantImprovement.ActualCanonicalMetricEnergyGraph.canonicalMetricValue_norm_sq_le_energy
#print axioms KLSConstantImprovement.ActualCanonicalMetricEnergyGraph.canonicalMetricEnergy_isCoercive

import OrderedOneFormKernel
import TensorExteriorCompactDomain
import CompactPotentialZeroCurvatureTest

/-! Actual compact weighted potential divergences in the constrained
one-form Hilbert space, together with their literal auxiliary-degree-zero
exterior derivative. The general Bochner Y has full ordered symmetry;
no compatible/curl-free condition on Y is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open MeasureTheory InnerProductSpace Set Matrix Filter LinearPMap
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n q r : ℕ} {φ ψ : Space n → ℝ}

lemma tensorAdjointDivergence_symmetric
    {F : OrderedTensorIndex n (r+1) → Space n → ℝ}
    (hs : classicalTensorSymmetric F) : classicalTensorSymmetric (tensorAdjointDivergence φ F) := by
  intro I J hp
  funext x
  unfold tensorAdjointDivergence
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [hs (Fin.cons j I) (Fin.cons j J) (by simpa only [List.ofFn_cons] using hp.cons j)]

lemma tensorAdjointDivergence_contDiff_infty
    {F : OrderedTensorIndex n (r+1) → Space n → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hF : ∀ I, ContDiff ℝ (⊤ : ℕ∞) (F I))
    (I : OrderedTensorIndex n r) :
    ContDiff ℝ (⊤ : ℕ∞) (tensorAdjointDivergence φ F I) := by
  unfold tensorAdjointDivergence weightedDerivativeTest
  apply ContDiff.neg
  apply ContDiff.sum
  intro j _
  exact (contDiff_coordinateDerivative (hF _) (m := (⊤ : ℕ∞)) (by simp) j).sub
    ((hF _).mul (contDiff_coordinateDerivative hφ (m := (⊤ : ℕ∞)) (by simp) j))

lemma tensorAdjointDivergenceLp_mem_symmetric
    {F : OrderedTensorIndex n (r+1) → Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hF : ∀ I, ContDiff ℝ 2 (F I))
    (hc : ∀ I, HasCompactSupport (F I)) (hs : classicalTensorSymmetric F) :
    tensorAdjointDivergenceLp hφ hF hc ∈ orderedTensorSymmetricSubspace φ r := by
  rw [mem_orderedTensorSymmetricSubspace_iff]
  intro I J hp
  apply Lp.ext
  filter_upwards [tensorAdjointDivergenceLp_ae hφ hF hc I,
    tensorAdjointDivergenceLp_ae hφ hF hc J] with x hx hy
  rw [hx,hy,congrFun (tensorAdjointDivergence_symmetric hs I J hp) x]

 def compactPotentialOneFormAdjointDivergenceLp (hφ : ContDiff ℝ 2 φ)
     (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (r : ℕ) :
     OrderedTensorField φ r :=
   tensorAdjointDivergenceLp hφ
     (fun I => (coordinatePotentialTensor_contDiff hψ (r+1) I).of_le (by simp))
     (coordinatePotentialTensor_hasCompactSupport hc (r+1))

 lemma compactPotentialOneFormAdjointDivergenceLp_mem_symmetric (hφ : ContDiff ℝ 2 φ)
     (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (r : ℕ) :
     compactPotentialOneFormAdjointDivergenceLp hφ hψ hc r ∈ orderedTensorSymmetricSubspace φ r :=
   tensorAdjointDivergenceLp_mem_symmetric hφ _ _ (coordinatePotentialTensor_symmetric hψ (r+1))

 def compactPotentialAdjointOneFormL2 (hφ : ContDiff ℝ 2 φ)
     (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (q : ℕ) : TensorOneFormL2 φ q :=
   symmetricOrderedOneFormLIE φ q
     ⟨compactPotentialOneFormAdjointDivergenceLp hφ hψ hc (q+1),
       compactPotentialOneFormAdjointDivergenceLp_mem_symmetric hφ hψ hc (q+1)⟩

 def compactPotentialAdjointOneFormL2_coefficient (φ ψ : Space n → ℝ) (q : ℕ) :
     TensorOneFormIndex n q → Space n → ℝ :=
   fun a => tensorAdjointDivergence φ (coordinatePotentialTensor ψ (q+2)) (Fin.cons a.2 a.1)

 lemma compactPotentialAdjointOneFormL2_coefficient_memLp (hφ : ContDiff ℝ 2 φ)
     (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (q : ℕ)
     (a : TensorOneFormIndex n q) :
     MemLp (compactPotentialAdjointOneFormL2_coefficient φ ψ q a)
       2 (potentialMeasure φ) :=
   memLp_of_continuous_hasCompactSupport hφ.continuous
     (contDiff_tensorAdjointDivergence hφ
       (fun I => (coordinatePotentialTensor_contDiff hψ (q+2) I).of_le (by simp))
       (Fin.cons a.2 a.1)).continuous
     (hasCompactSupport_tensorAdjointDivergence (coordinatePotentialTensor_hasCompactSupport hc (q+2))
       (Fin.cons a.2 a.1))

 lemma compactPotentialAdjointOneFormL2_coe_finiteMatrix (hφ : ContDiff ℝ 2 φ)
     (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (q : ℕ) :
     (compactPotentialAdjointOneFormL2 hφ hψ hc q).val =
       finiteMatrixLp (compactPotentialAdjointOneFormL2_coefficient φ ψ q)
         (compactPotentialAdjointOneFormL2_coefficient_memLp hφ hψ hc q) := by
   apply PiLp.ext
   intro a
   change compactPotentialOneFormAdjointDivergenceLp hφ hψ hc (q+1) (Fin.cons a.2 a.1) =
     (compactPotentialAdjointOneFormL2_coefficient_memLp hφ hψ hc q a).toLp _
   apply Lp.ext
   exact (tensorAdjointDivergenceLp_ae hφ
     (fun I => (coordinatePotentialTensor_contDiff hψ (q+2) I).of_le (by simp))
     (coordinatePotentialTensor_hasCompactSupport hc (q+2)) (Fin.cons a.2 a.1)).trans
       (compactPotentialAdjointOneFormL2_coefficient_memLp hφ hψ hc q a).coeFn_toLp.symm

 theorem compactPotentialAdjointOneFormL2_mem_compactSmooth (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
     (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (q : ℕ) :
     compactPotentialAdjointOneFormL2 (hφ.of_le (by simp)) hψ hc q ∈
       compactSmoothFiberSet φ (tensorOneFormConstraintMatrix n q) := by
   refine ⟨compactPotentialAdjointOneFormL2_coefficient φ ψ q, ?_, ?_, ?_⟩
   · intro a
     exact tensorAdjointDivergence_contDiff_infty hφ (coordinatePotentialTensor_contDiff hψ (q+2)) _
   · intro a
     exact hasCompactSupport_tensorAdjointDivergence (coordinatePotentialTensor_hasCompactSupport hc (q+2)) _
   · exact ⟨_, compactPotentialAdjointOneFormL2_coe_finiteMatrix _ hψ hc q⟩

 theorem compactPotentialAdjointOneFormL2_mem_domain (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
     (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (q : ℕ) :
     compactPotentialAdjointOneFormL2 (hφ.of_le (by simp)) hψ hc q ∈
       (tensorExteriorOneOperator (hφ.of_le (by simp)) q).domain :=
   compactSmoothFiberSet_subset_exteriorOne_domain (hφ.of_le (by simp)) q
     (compactPotentialAdjointOneFormL2_mem_compactSmooth hφ hψ hc q)

 lemma compactPotentialAdjointOneFormL2_residual_norm (hφ : ContDiff ℝ 2 φ)
     (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (q : ℕ) :
     ‖compactPotentialAdjointOneFormL2 hφ hψ hc q -
       closedPartialKernelProjection (tensorExteriorOneOperator (hφ.of_le (by simp)) q)
         (tensorExteriorOneOperator_isClosed _ q) (compactPotentialAdjointOneFormL2 hφ hψ hc q)‖ =
       ‖compactPotentialOneFormAdjointDivergenceLp hφ hψ hc (q+1) -
         tensorCompactProjection (hφ.of_le (by simp)) (q+1)
           (compactPotentialOneFormAdjointDivergenceLp hφ hψ hc (q+1))‖ :=
   symmetricOrderedOneForm_residual_norm _ _

 theorem compactPotentialAdjointOneFormL2_zero_differential (hφ : ContDiff ℝ 2 φ)
     (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (z : TensorTwoFormIndex n 0) (x : Space n) :
     tensorExteriorOneDifferential
       (fun a => tensorAdjointDivergence φ (coordinatePotentialTensor ψ 2) (Fin.cons a.2 a.1)) z x =
       tensorCurvatureCurlZero (coordinateHessian φ x) (fun I => coordinatePotentialTensor ψ 2 I x) z := by
   change (1/Real.sqrt 2) *
     (coordinateDerivative (tensorAdjointDivergence φ (coordinatePotentialTensor ψ 2) (Fin.cons z.2.2 z.1)) z.2.1 x -
       coordinateDerivative (tensorAdjointDivergence φ (coordinatePotentialTensor ψ 2) (Fin.cons z.2.1 z.1)) z.2.2 x) = _
   rw [tensorAdjointDivergence_curl hφ
     (fun I => (coordinatePotentialTensor_contDiff hψ 2 I).of_le (by simp))
     (coordinatePotentialTensor_symmetric hψ 2) (coordinatePotentialTensor_compatible hψ 1)]
   rfl

 theorem compactPotentialCurvatureCurlZeroLp_mem_twoForm (hφ : ContDiff ℝ 2 φ)
     (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
     compactPotentialCurvatureCurlZeroLp hφ hψ hc ∈ tensorTwoFormL2Subspace φ 0 := by
   apply (finiteMatrixLp_mem_twoForm_iff _).mpr
   apply Eventually.of_forall
   intro x
   have hpoint (y : Space n) : WithLp.toLp 2
       (fun a : TensorOneFormIndex n 0 => tensorAdjointDivergence φ (coordinatePotentialTensor ψ 2)
         (Fin.cons a.2 a.1) y) ∈ tensorOneFormSymmetricFiber n 0 := by
     rw [tensorOneFormSymmetricFiber_zero]
     trivial
   have he := tensorExteriorOneDifferential_compatible hpoint x
   simpa only [compactPotentialAdjointOneFormL2_zero_differential hφ hψ] using he

 def compactPotentialCurvatureCurlZeroTwoForm (hφ : ContDiff ℝ 2 φ)
     (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) : TensorTwoFormL2 φ 0 :=
   ⟨compactPotentialCurvatureCurlZeroLp hφ hψ hc, compactPotentialCurvatureCurlZeroLp_mem_twoForm hφ hψ hc⟩

 theorem compactPotentialAdjointOneFormL2_zero_graph (hφ : ContDiff ℝ 2 φ)
     (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
     (compactPotentialAdjointOneFormL2 hφ hψ hc 0, compactPotentialCurvatureCurlZeroTwoForm hφ hψ hc) ∈
       (tensorExteriorOneOperator (hφ.of_le (by simp)) 0).graph := by
   let f : TensorOneFormIndex n 0 → Space n → ℝ := compactPotentialAdjointOneFormL2_coefficient φ ψ 0
   let hf := compactPotentialAdjointOneFormL2_coefficient_memLp hφ hψ hc 0
   let g : TensorTwoFormIndex n 0 → Space n → ℝ := fun z x =>
     tensorCurvatureCurlZero (coordinateHessian φ x) (fun I => coordinatePotentialTensor ψ 2 I x) z
   let hg := compactPotentialCurvatureCurlZero_memLp hφ hψ hc
   have hfm : finiteMatrixLp f hf ∈ tensorOneFormL2Subspace φ 0 := by
     rw [← compactPotentialAdjointOneFormL2_coe_finiteMatrix hφ hψ hc 0]
     exact (compactPotentialAdjointOneFormL2 hφ hψ hc 0).property
   have hgm : finiteMatrixLp g hg ∈ tensorTwoFormL2Subspace φ 0 :=
     compactPotentialCurvatureCurlZeroLp_mem_twoForm hφ hψ hc
   have hw : HasWeakMatrixDerivative (tensorExteriorOneDerivativeMatrix n 0) f g := by
     have he : matrixDifferential (tensorExteriorOneDerivativeMatrix n 0) f = g := by
       funext z x
       rw [tensorExteriorOne_matrixDifferential]
       exact compactPotentialAdjointOneFormL2_zero_differential hφ hψ z x
     exact he ▸ matrixDifferential_hasWeakMatrixDerivative (tensorExteriorOneDerivativeMatrix n 0)
       (fun a => contDiff_tensorAdjointDivergence hφ
         (fun I => (coordinatePotentialTensor_contDiff hψ 2 I).of_le (by simp)) _)
   have hgraph := finiteMatrixLp_mem_weightedMatrixFiberGraph (hφ.of_le (by simp))
     (tensorExteriorOneDerivativeMatrix n 0) (tensorOneFormL2Subspace φ 0)
     (tensorTwoFormL2Subspace φ 0) hf hg hfm hgm hw
   change _ ∈ (weightedMatrixFiberOperator _ _ _ _).graph
   rw [weightedMatrixFiberOperator_graph]
   exact hgraph

 theorem compactPotentialAdjointOneFormL2_zero_apply (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
     (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
     tensorExteriorOneOperator (hφ.of_le (by simp)) 0
       ⟨compactPotentialAdjointOneFormL2 (hφ.of_le (by simp)) hψ hc 0,
         compactPotentialAdjointOneFormL2_mem_domain hφ hψ hc 0⟩ =
       compactPotentialCurvatureCurlZeroTwoForm (hφ.of_le (by simp)) hψ hc := by
   rcases (tensorExteriorOneOperator (hφ.of_le (by simp)) 0).mem_graph_iff.mp
     (compactPotentialAdjointOneFormL2_zero_graph (hφ.of_le (by simp)) hψ hc) with ⟨u,hu,hAu⟩
   have he : u = ⟨compactPotentialAdjointOneFormL2 (hφ.of_le (by simp)) hψ hc 0,
       compactPotentialAdjointOneFormL2_mem_domain hφ hψ hc 0⟩ := Subtype.ext hu
   rw [he] at hAu
   exact hAu

end KLS.DeterministicBridgeIntegration
end
#print axioms KLS.DeterministicBridgeIntegration.compactPotentialAdjointOneFormL2_mem_domain
#print axioms KLS.DeterministicBridgeIntegration.compactPotentialAdjointOneFormL2_zero_apply
#print axioms KLS.DeterministicBridgeIntegration.compactPotentialAdjointOneFormL2_residual_norm

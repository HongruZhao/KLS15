import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! The variational projection identity for an actual closed Hilbert
complex. Operators are genuine partially defined linear operators and the
adjoint is mathlib's Hilbert adjoint. No closed-range or inverse premise. -/
noncomputable section
open Set Filter InnerProductSpace LinearPMap WithLp
open scoped Topology RealInnerProductSpace
namespace KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false
variable {E F G : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

 theorem closed_partial_operator_kernel_isClosed (A : E →ₗ.[ℝ] F) (hA : A.IsClosed) :
     IsClosed (A.ker : Set E) := by
   have he : (A.ker : Set E) = (fun x : E => (x,(0 : F))) ⁻¹' (A.graph : Set (E × F)) := by
     ext x
     change x ∈ A.ker ↔ (x,(0 : F)) ∈ A.graph
     constructor
     · intro hx
       rcases LinearPMap.mem_ker_iff.mp hx with ⟨v,hv,hAv⟩
       exact A.mem_graph_iff.mpr ⟨v,hv.symm,hAv⟩
     · intro hx
       rcases A.mem_graph_iff.mp hx with ⟨v,hv,hAv⟩
       exact LinearPMap.mem_ker_iff.mpr ⟨v,hv.symm,hAv⟩
   rw [he]
   exact hA.preimage (continuous_id.prodMk continuous_const)

 theorem closed_partial_adjoint_range_orthogonal
     (A : E →ₗ.[ℝ] F) (hA : A.IsClosed) (hd : Dense (A.domain : Set E)) :
     (LinearMap.range A.adjoint.toFun).orthogonal=A.ker := by
   apply le_antisymm
   · intro x hx
     let Γ : Submodule ℝ (WithLp 2 (E × F)) :=
       A.graph.comap (WithLp.linearEquiv 2 ℝ (E × F)).toLinearMap
     have hcΓ : IsClosed (Γ : Set (WithLp 2 (E × F))) :=
       hA.preimage (WithLp.prod_continuous_ofLp 2 E F)
     letI : CompleteSpace Γ := hcΓ.completeSpace_coe
     have hz : WithLp.toLp 2 (x,(0 : F)) ∈ Γ.orthogonal.orthogonal := by
       apply (Γ.orthogonal.mem_orthogonal _).mpr
       intro w hw
       have ht (v : A.domain) :
           inner ℝ (v : E) (WithLp.ofLp w).1 + inner ℝ (A v) (WithLp.ofLp w).2=0 := by
         have hv : WithLp.toLp 2 ((v : E),A v) ∈ Γ := A.mem_graph v
         have hh := (Γ.mem_orthogonal _).mp hw _ hv
         simpa only [WithLp.prod_inner_apply,WithLp.ofLp_toLp] using hh
       have hb : (WithLp.ofLp w).2 ∈ A.adjoint.domain := by
         apply A.mem_adjoint_domain_of_exists
         refine ⟨-(WithLp.ofLp w).1,?_⟩
         intro v
         have hh := ht v
         rw [inner_neg_left]
         have hc₁ := real_inner_comm (v : E) (WithLp.ofLp w).1
         have hc₂ := real_inner_comm (A v) (WithLp.ofLp w).2
         linarith
       have ha : A.adjoint ⟨(WithLp.ofLp w).2,hb⟩= -(WithLp.ofLp w).1 := by
         apply LinearPMap.adjoint_apply_eq hd
         intro v
         have hh := ht v
         rw [inner_neg_left]
         have hc₁ := real_inner_comm (v : E) (WithLp.ofLp w).1
         have hc₂ := real_inner_comm (A v) (WithLp.ofLp w).2
         linarith
       have hzero := ((LinearMap.range A.adjoint.toFun).mem_orthogonal _).mp hx
         (A.adjoint ⟨(WithLp.ofLp w).2,hb⟩) ⟨_,rfl⟩
       rw [ha,inner_neg_left,neg_eq_zero] at hzero
       simpa only [WithLp.prod_inner_apply,WithLp.ofLp_toLp,inner_zero_right,add_zero] using hzero
     rw [Γ.orthogonal_orthogonal] at hz
     have hg : (x,(0 : F)) ∈ A.graph := hz
     rcases (A.mem_graph_iff).mp hg with ⟨v,hv,hAv⟩
     exact A.mem_ker_iff.mpr ⟨v,hv.symm,hAv⟩
   · intro x hx
     rcases A.mem_ker_iff.mp hx with ⟨v,rfl,hv⟩
     apply (LinearMap.range A.adjoint.toFun).mem_orthogonal _ |>.mpr
     rintro y ⟨ω,rfl⟩
     change inner ℝ (A.adjoint ω) (v : E)=0
     calc
       _ = inner ℝ (ω : F) (A v) := LinearPMap.adjoint_isFormalAdjoint hd ω v
       _ = 0 := by rw [hv,inner_zero_right]


 def closedPartialKernelProjection (A : E →ₗ.[ℝ] F) (hA : A.IsClosed) : E →L[ℝ] E := by
   letI : CompleteSpace A.ker := (closed_partial_operator_kernel_isClosed A hA).completeSpace_coe
   exact A.ker.starProjection

 theorem closedPartialKernelProjection_mem (A : E →ₗ.[ℝ] F) (hA : A.IsClosed) (u : E) :
     closedPartialKernelProjection A hA u ∈ A.ker := by
   letI : CompleteSpace A.ker := (closed_partial_operator_kernel_isClosed A hA).completeSpace_coe
   change A.ker.starProjection u ∈ A.ker
   exact A.ker.starProjection_apply_mem u

 theorem closedPartialResidual_mem_orthogonal (A : E →ₗ.[ℝ] F) (hA : A.IsClosed) (u : E) :
     u-closedPartialKernelProjection A hA u ∈ A.ker.orthogonal := by
   letI : CompleteSpace A.ker := (closed_partial_operator_kernel_isClosed A hA).completeSpace_coe
   change u-A.ker.starProjection u ∈ A.ker.orthogonal
   exact A.ker.sub_starProjection_mem_orthogonal u

 theorem hilbert_complex_project_adjoint
     (A : E →ₗ.[ℝ] F) (B : F →ₗ.[ℝ] G)
     (hd : Dense (A.domain : Set E)) (hB : B.IsClosed)
     (hcomplex : ∀ v : A.domain, A v ∈ B.ker) (ω : A.adjoint.domain) :
     ∃ η : A.adjoint.domain, ∃ hη : (η : F) ∈ B.domain,
       B ⟨(η : F),hη⟩=0 ∧ A.adjoint η=A.adjoint ω := by
   let P := closedPartialKernelProjection B hB
   have hP : P (ω : F) ∈ B.ker := closedPartialKernelProjection_mem B hB ω
   have hp (v : A.domain) : inner ℝ (A.adjoint ω) (v : E)=inner ℝ (P ω) (A v) := by
     have he := (closedPartialResidual_mem_orthogonal B hB (ω : F))
     have hz := (B.ker.mem_orthogonal' _).mp he (A v) (hcomplex v)
     change inner ℝ ((ω : F)-P ω) (A v)=0 at hz
     rw [inner_sub_left] at hz
     calc
       _ = inner ℝ (ω : F) (A v) := LinearPMap.adjoint_isFormalAdjoint hd ω v
       _ = _ := by linarith
   have hPa : P (ω : F) ∈ A.adjoint.domain :=
     A.mem_adjoint_domain_of_exists _ ⟨A.adjoint ω,hp⟩
   let η : A.adjoint.domain := ⟨P (ω : F),hPa⟩
   have hη : (η : F) ∈ B.domain := B.ker_le_domain hP
   refine ⟨η,hη,?_,?_⟩
   · exact LinearPMap.coe_mem_ker_iff.mp hP
   · exact LinearPMap.adjoint_apply_eq hd η hp

 def hilbertComplexVariationalValues (A : E →ₗ.[ℝ] F) (B : F →ₗ.[ℝ] G) (u : E) : Set ℝ :=
   {t | ∃ ω : A.adjoint.domain, ∃ hω : (ω : F) ∈ B.domain,
     t=2*inner ℝ u (A.adjoint ω)-‖A.adjoint ω‖^2-‖B ⟨(ω : F),hω⟩‖^2}

 theorem hilbert_complex_variational_upper
     (A : E →ₗ.[ℝ] F) (B : F →ₗ.[ℝ] G)
     (hA : A.IsClosed) (hd : Dense (A.domain : Set E)) (u : E) :
     ‖u-closedPartialKernelProjection A hA u‖^2 ∈ upperBounds (hilbertComplexVariationalValues A B u) := by
   rintro t ⟨ω,hω,rfl⟩
   let z := A.adjoint ω
   let R := u-closedPartialKernelProjection A hA u
   have hP : closedPartialKernelProjection A hA u ∈ (LinearMap.range A.adjoint.toFun).orthogonal := by
     rw [closed_partial_adjoint_range_orthogonal A hA hd]
     exact closedPartialKernelProjection_mem A hA u
   have hz := ((LinearMap.range A.adjoint.toFun).mem_orthogonal _).mp hP z ⟨ω,rfl⟩
   have hip : inner ℝ u z=inner ℝ R z := by
     change _=inner ℝ (u-closedPartialKernelProjection A hA u) z
     rw [inner_sub_left]
     have hc := real_inner_comm z (closedPartialKernelProjection A hA u)
     linarith
   have hs := norm_sub_sq_real R z
   have hnon := sq_nonneg ‖R-z‖
   have hbn := sq_nonneg ‖B ⟨(ω : F),hω⟩‖
   change 2*inner ℝ u z-‖z‖^2-‖B ⟨(ω : F),hω⟩‖^2 ≤ ‖R‖^2
   rw [hip]
   linarith

 theorem hilbert_complex_variational_isLUB
     (A : E →ₗ.[ℝ] F) (B : F →ₗ.[ℝ] G)
     (hA : A.IsClosed) (hd : Dense (A.domain : Set E)) (hB : B.IsClosed)
     (hcomplex : ∀ v : A.domain, A v ∈ B.ker) (u : E) :
     IsLUB (hilbertComplexVariationalValues A B u)
       (‖u-closedPartialKernelProjection A hA u‖^2) := by
   refine ⟨hilbert_complex_variational_upper A B hA hd u,?_⟩
   intro M hM
   let R := u-closedPartialKernelProjection A hA u
   have hr : R ∈ (LinearMap.range A.adjoint.toFun).topologicalClosure := by
     rw [←Submodule.orthogonal_orthogonal_eq_closure,closed_partial_adjoint_range_orthogonal A hA hd]
     exact closedPartialResidual_mem_orthogonal A hA u
   have hzbound : ∀ z ∈ LinearMap.range A.adjoint.toFun,
       2*inner ℝ u z-‖z‖^2 ≤ M := by
     rintro z ⟨ω,rfl⟩
     obtain ⟨η,hη,hBη,hAη⟩ := hilbert_complex_project_adjoint A B hd hB hcomplex ω
     have hh := hM (show 2*inner ℝ u (A.adjoint η)-‖A.adjoint η‖^2-‖B ⟨(η : F),hη⟩‖^2 ∈
         hilbertComplexVariationalValues A B u from ⟨η,hη,rfl⟩)
     change 2*inner ℝ u (A.adjoint ω)-‖A.adjoint ω‖^2 ≤ M
     simpa only [hAη,hBη,norm_zero,zero_pow (by norm_num : (2 : ℕ)≠0),sub_zero] using hh
   have hc : IsClosed {z : E | 2*inner ℝ u z-‖z‖^2 ≤ M} :=
     isClosed_le ((continuous_const.mul (continuous_const.inner continuous_id)).sub
       (continuous_norm.pow 2)) continuous_const
   have hR : 2*inner ℝ u R-‖R‖^2 ≤ M :=
     (closure_minimal hzbound hc) hr
   have hz := (A.ker.mem_orthogonal _).mp (closedPartialResidual_mem_orthogonal A hA u)
     _ (closedPartialKernelProjection_mem A hA u)
   have hi : inner ℝ u R=‖R‖^2 := by
     calc
       _ = inner ℝ (R+closedPartialKernelProjection A hA u) R := by
         congr 1
         dsimp only [R]
         abel
       _ = _ := by rw [inner_add_left,real_inner_self_eq_norm_sq,hz,add_zero]
   rw [hi] at hR
   change ‖R‖^2 ≤ M
   linarith

 theorem hilbert_complex_residual_bound_of_variational_bound
     (A : E →ₗ.[ℝ] F) (B : F →ₗ.[ℝ] G)
     (hA : A.IsClosed) (hd : Dense (A.domain : Set E)) (hB : B.IsClosed)
     (hcomplex : ∀ v : A.domain, A v ∈ B.ker) (u : E) {M : ℝ}
     (hbound : ∀ ω : A.adjoint.domain, ∀ hω : (ω : F) ∈ B.domain,
       2*inner ℝ u (A.adjoint ω)-‖A.adjoint ω‖^2-‖B ⟨(ω : F),hω⟩‖^2 ≤ M) :
     ‖u-closedPartialKernelProjection A hA u‖^2 ≤ M := by
   apply (hilbert_complex_variational_isLUB A B hA hd hB hcomplex u).2
   rintro t ⟨ω,hω,rfl⟩
   exact hbound ω hω


 theorem hilbert_complex_residual_bound_of_differential_test_bound
     (A : E →ₗ.[ℝ] F) (B : F →ₗ.[ℝ] G)
     (hA : A.IsClosed) (hd : Dense (A.domain : Set E)) (hB : B.IsClosed)
     (hcomplex : ∀ v : A.domain, A v ∈ B.ker) (u : A.domain) {M : ℝ}
     (hbound : ∀ ω : A.adjoint.domain, ∀ hω : (ω : F) ∈ B.domain,
       2*inner ℝ (A u) (ω : F)-‖A.adjoint ω‖^2-‖B ⟨(ω : F),hω⟩‖^2 ≤ M) :
     ‖(u : E)-closedPartialKernelProjection A hA u‖^2 ≤ M := by
   apply hilbert_complex_residual_bound_of_variational_bound A B hA hd hB hcomplex (u : E)
   intro ω hω
   have hi : inner ℝ (A u) (ω : F)=inner ℝ (u : E) (A.adjoint ω) :=
     (LinearPMap.adjoint_isFormalAdjoint hd).symm u ω
   rw [←hi]
   exact hbound ω hω

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.closed_partial_adjoint_range_orthogonal
#print axioms KLS.DeterministicBridgeIntegration.hilbert_complex_project_adjoint
#print axioms KLS.DeterministicBridgeIntegration.hilbert_complex_variational_isLUB
#print axioms KLS.DeterministicBridgeIntegration.hilbert_complex_residual_bound_of_variational_bound

#print axioms KLS.DeterministicBridgeIntegration.hilbert_complex_residual_bound_of_differential_test_bound

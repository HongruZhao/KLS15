import CompactPotentialBochnerSplit

/-! Literal physical completed square for auxiliary degree zero, i.e.
the rank-one compatibility correction. Coordinates retain the unique
empty auxiliary tuple and the normalized ordered exterior coefficients. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3

 def tensorCurvatureContractionZero (v : Fin n → ℝ) (F : OrderedTensorIndex n 2 → ℝ) :
     EuclideanSpace ℝ (TensorOneFormIndex n 0) :=
   WithLp.toLp 2 (fun a => ∑ j, v j*F (Fin.cons j (Fin.cons a.2 a.1)))

 def tensorTwoFormInteriorZero (v : Fin n → ℝ) (f : TensorTwoFormIndex n 0 → ℝ) :
     EuclideanSpace ℝ (TensorOneFormIndex n 0) :=
   WithLp.toLp 2 (fun a => ∑ i, v i*f (a.1,i,a.2))

 def tensorCurvatureCurlZero (K : Matrix (Fin n) (Fin n) ℝ) (F : OrderedTensorIndex n 2 → ℝ) :
     EuclideanSpace ℝ (TensorTwoFormIndex n 0) :=
   WithLp.toLp 2 (fun a => (1/Real.sqrt 2)*∑ j,
     (K a.2.1 j*F (Fin.cons j (Fin.cons a.2.2 a.1))-
       K a.2.2 j*F (Fin.cons j (Fin.cons a.2.1 a.1))))

 def tensorTwoFormCurvatureZero (K : Matrix (Fin n) (Fin n) ℝ)
     (f : TensorTwoFormIndex n 0 → ℝ) : ℝ :=
   2*∑ I : OrderedTensorIndex n 0, ∑ i, ∑ j, ∑ k,
     K i j*f (I,i,k)*f (I,j,k)

 lemma tensorPhysicalCurvatureForm_rank_one_zero (v : Fin n → ℝ) (F : OrderedTensorIndex n 2 → ℝ) :
     tensorPhysicalCurvatureForm (fun i j => v i*v j) F=‖tensorCurvatureContractionZero v F‖^2 := by
   unfold tensorPhysicalCurvatureForm
   simp_rw [finite_rank_one_quadratic]
   rw [PiLp.norm_sq_eq_of_L2]
   simp only [tensorCurvatureContractionZero,PiLp.toLp_apply,Real.norm_eq_abs,sq_abs,Fintype.sum_prod_type]
   symm
   exact sum_ordered_tensor_cons (r := 0) (fun J => (∑ i, v i*F (Fin.cons i J))^2)

 lemma tensorTwoFormCurvatureZero_rank_one (v : Fin n → ℝ) (f : TensorTwoFormIndex n 0 → ℝ) :
     tensorTwoFormCurvatureZero (fun i j => v i*v j) f=2*‖tensorTwoFormInteriorZero v f‖^2 := by
   unfold tensorTwoFormCurvatureZero
   rw [PiLp.norm_sq_eq_of_L2]
   simp only [tensorTwoFormInteriorZero,PiLp.toLp_apply,Real.norm_eq_abs,sq_abs,Fintype.sum_prod_type]
   congr 1
   apply Finset.sum_congr rfl
   intro I _
   calc
     _ = ∑ k, ∑ i, ∑ j, (v i*v j)*f (I,i,k)*f (I,j,k) :=
       (finite_triple_sum_last_to_first _).symm
     _ = _ := by simp_rw [finite_rank_one_quadratic]

 lemma tensorCurvatureCurlZero_rank_one_apply (v : Fin n → ℝ) (F : OrderedTensorIndex n 2 → ℝ)
     (I : OrderedTensorIndex n 0) (i j : Fin n) :
     tensorCurvatureCurlZero (fun i j => v i*v j) F (I,i,j)=
       (1/Real.sqrt 2)*(v i*tensorCurvatureContractionZero v F (I,j)-
         v j*tensorCurvatureContractionZero v F (I,i)) := by
   change (1/Real.sqrt 2)*(∑ k, ((v i*v k)*F (Fin.cons k (Fin.cons j I))-
     (v j*v k)*F (Fin.cons k (Fin.cons i I))))=_
   simp only [Finset.sum_sub_distrib,tensorCurvatureContractionZero,PiLp.toLp_apply,
     Finset.mul_sum,mul_assoc]

 lemma tensorCurvatureCurlZero_rank_one_pairing (v : Fin n → ℝ) (F : OrderedTensorIndex n 2 → ℝ)
     (f : TensorTwoFormIndex n 0 → ℝ) (hf : ∀ I i j, f (I,i,j)= -f (I,j,i)) :
     inner ℝ (tensorCurvatureCurlZero (fun i j => v i*v j) F) (WithLp.toLp 2 f)=
       Real.sqrt 2*inner ℝ (tensorCurvatureContractionZero v F) (tensorTwoFormInteriorZero v f) := by
   have he (I : OrderedTensorIndex n 0) := finite_skew_pairing v
     (fun i => tensorCurvatureContractionZero v F (I,i)) (fun i j => f (I,i,j)) (hf I)
   simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,Fintype.sum_prod_type,PiLp.toLp_apply]
   simp_rw [tensorCurvatureCurlZero_rank_one_apply]
   have hl : (∑ I : OrderedTensorIndex n 0, ∑ i, ∑ j,
       f (I,i,j)*((1/Real.sqrt 2)*(v i*tensorCurvatureContractionZero v F (I,j)-
         v j*tensorCurvatureContractionZero v F (I,i)))) =
       (1/Real.sqrt 2)*2*∑ I : OrderedTensorIndex n 0, ∑ j,
         tensorCurvatureContractionZero v F (I,j)*(∑ i, v i*f (I,i,j)) := by
     simp_rw [mul_left_comm (f _) (1/Real.sqrt 2),←Finset.mul_sum]
     simp_rw [mul_comm (f _),he]
     simp only [←Finset.mul_sum,mul_assoc]
   rw [hl]
   have hs : (1/Real.sqrt 2)*2=Real.sqrt 2 := by
     calc
       _ = 2/Real.sqrt 2 := by ring
       _ = Real.sqrt 2 := (div_eq_iff (Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2))).2
         (by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)])
   rw [hs]
   congr 1
   simp only [tensorTwoFormInteriorZero,PiLp.toLp_apply,mul_comm]

 def tensorCurvatureCouplingFormZero (K : Matrix (Fin n) (Fin n) ℝ)
     (F : OrderedTensorIndex n 2 → ℝ) (f : TensorTwoFormIndex n 0 → ℝ) : ℝ :=
   tensorPhysicalCurvatureForm K F-2*inner ℝ (tensorCurvatureCurlZero K F) (WithLp.toLp 2 f)+
     tensorTwoFormCurvatureZero K f

 theorem tensorCurvatureCouplingZero_rank_one_nonneg (v : Fin n → ℝ) (F : OrderedTensorIndex n 2 → ℝ)
     (f : TensorTwoFormIndex n 0 → ℝ) (hf : ∀ I i j, f (I,i,j)= -f (I,j,i)) :
     0 ≤ tensorCurvatureCouplingFormZero (fun i j => v i*v j) F f := by
   unfold tensorCurvatureCouplingFormZero
   rw [tensorPhysicalCurvatureForm_rank_one_zero,tensorCurvatureCurlZero_rank_one_pairing v F f hf,
     tensorTwoFormCurvatureZero_rank_one]
   have h := sq_nonneg ‖tensorCurvatureContractionZero v F-Real.sqrt 2 • tensorTwoFormInteriorZero v f‖
   rw [norm_sub_sq_real,real_inner_smul_right,norm_smul,mul_pow,
     Real.norm_eq_abs,sq_abs,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)] at h
   nlinarith


 lemma tensorCurvatureCurlZero_add (K L : Matrix (Fin n) (Fin n) ℝ) (F : OrderedTensorIndex n 2 → ℝ) :
     tensorCurvatureCurlZero (K+L) F=tensorCurvatureCurlZero K F+tensorCurvatureCurlZero L F := by
   apply PiLp.ext
   intro a
   change (1/Real.sqrt 2)*∑ j,
     ((K a.2.1 j+L a.2.1 j)*F (Fin.cons j (Fin.cons a.2.2 a.1))-
       (K a.2.2 j+L a.2.2 j)*F (Fin.cons j (Fin.cons a.2.1 a.1)))=_
   simp only [add_mul,Finset.sum_sub_distrib,Finset.sum_add_distrib,tensorCurvatureCurlZero,
     PiLp.toLp_apply,PiLp.add_apply]
   ring

 lemma tensorTwoFormCurvatureZero_add (K L : Matrix (Fin n) (Fin n) ℝ) (f : TensorTwoFormIndex n 0 → ℝ) :
     tensorTwoFormCurvatureZero (K+L) f=tensorTwoFormCurvatureZero K f+tensorTwoFormCurvatureZero L f := by
   simp only [tensorTwoFormCurvatureZero,Matrix.add_apply,add_mul,Finset.sum_add_distrib]
   ring

 lemma tensorCurvatureCouplingFormZero_add (K L : Matrix (Fin n) (Fin n) ℝ)
     (F : OrderedTensorIndex n 2 → ℝ) (f : TensorTwoFormIndex n 0 → ℝ) :
     tensorCurvatureCouplingFormZero (K+L) F f=
       tensorCurvatureCouplingFormZero K F f+tensorCurvatureCouplingFormZero L F f := by
   unfold tensorCurvatureCouplingFormZero
   rw [tensorPhysicalCurvatureForm_add,tensorCurvatureCurlZero_add,inner_add_left,tensorTwoFormCurvatureZero_add]
   ring

 lemma tensorCurvatureCouplingFormZero_zero (F : OrderedTensorIndex n 2 → ℝ) (f : TensorTwoFormIndex n 0 → ℝ) :
     tensorCurvatureCouplingFormZero 0 F f=0 := by
   have hzero : tensorCurvatureCurlZero 0 F=0 := by
     apply PiLp.ext
     intro a
     simp [tensorCurvatureCurlZero]
   simp [tensorCurvatureCouplingFormZero,tensorPhysicalCurvatureForm,hzero,tensorTwoFormCurvatureZero]

 lemma tensorCurvatureCouplingFormZero_sum {τ : Type*} (s : Finset τ) (K : τ → Matrix (Fin n) (Fin n) ℝ)
     (F : OrderedTensorIndex n 2 → ℝ) (f : TensorTwoFormIndex n 0 → ℝ) :
     tensorCurvatureCouplingFormZero (∑ t ∈ s, K t) F f=∑ t ∈ s, tensorCurvatureCouplingFormZero (K t) F f := by
   classical
   induction s using Finset.induction_on with
   | empty => simp [tensorCurvatureCouplingFormZero_zero]
   | @insert t s ht ih =>
     rw [Finset.sum_insert ht,Finset.sum_insert ht,tensorCurvatureCouplingFormZero_add,ih]

 theorem tensorCurvatureCouplingFormZero_nonneg (K : Matrix (Fin n) (Fin n) ℝ) (hK : K.PosSemidef)
     (F : OrderedTensorIndex n 2 → ℝ) (f : TensorTwoFormIndex n 0 → ℝ)
     (hf : ∀ I i j, f (I,i,j)= -f (I,j,i)) : 0 ≤ tensorCurvatureCouplingFormZero K F f := by
   obtain ⟨v,hv⟩ := positiveMatrix_row_gram K hK
   have he : K=∑ t : Fin n, (fun i j => v t i*v t j) := by
     ext i j
     simpa only [Finset.sum_apply] using hv i j
   rw [he,tensorCurvatureCouplingFormZero_sum]
   exact Finset.sum_nonneg (fun t _ => tensorCurvatureCouplingZero_rank_one_nonneg (v t) F f hf)

 lemma tensorCurvatureCurlZero_scalar_identity (a : ℝ) (F : OrderedTensorIndex n 2 → ℝ)
     (hs : ∀ I J, List.Perm (List.ofFn I) (List.ofFn J) → F I=F J) :
     tensorCurvatureCurlZero (a • (1 : Matrix (Fin n) (Fin n) ℝ)) F=0 := by
   apply PiLp.ext
   rintro ⟨I,i,j⟩
   change (1/Real.sqrt 2)*(∑ k,
     ((a • (1 : Matrix (Fin n) (Fin n) ℝ)) i k*F (Fin.cons k (Fin.cons j I))-
       (a • (1 : Matrix (Fin n) (Fin n) ℝ)) j k*F (Fin.cons k (Fin.cons i I))))=0
   simp only [Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,mul_ite,mul_one,mul_zero,
     ite_mul,zero_mul,Finset.sum_sub_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
   rw [hs (Fin.cons i (Fin.cons j I)) (Fin.cons j (Fin.cons i I))
     (by simpa only [List.ofFn_cons] using List.Perm.swap j i (List.ofFn I))]
   ring

 lemma tensorTwoFormCurvatureZero_scalar_nonneg {a : ℝ} (ha : 0 ≤ a) (f : TensorTwoFormIndex n 0 → ℝ) :
     0 ≤ tensorTwoFormCurvatureZero (a • (1 : Matrix (Fin n) (Fin n) ℝ)) f := by
   unfold tensorTwoFormCurvatureZero
   simp only [Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,mul_ite,mul_one,mul_zero,
     ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
   apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
   apply Finset.sum_nonneg
   intro I _
   apply Finset.sum_nonneg
   intro i _
   apply Finset.sum_nonneg
   intro k _
   by_cases hik : i=k
   · subst k
     simp only [ite_true]
     apply Finset.sum_nonneg
     intro j _
     nlinarith [sq_nonneg (f (I,i,j))]
   · simp only [hik,ite_false,Finset.sum_const_zero,le_refl]

 theorem tensorCurvatureCouplingFormZero_lower (K : Matrix (Fin n) (Fin n) ℝ) (hK : K.IsSymm)
     (F : OrderedTensorIndex n 2 → ℝ)
     (hs : ∀ I J, List.Perm (List.ofFn I) (List.ofFn J) → F I=F J)
     (f : TensorTwoFormIndex n 0 → ℝ) (hf : ∀ I i j, f (I,i,j)= -f (I,j,i))
     {a : ℝ} (ha : 0 ≤ a)
     (hlower : ∀ v : Fin n → ℝ, a*(v ⬝ᵥ v) ≤ v ⬝ᵥ (K *ᵥ v)) :
     a*(∑ I, (F I)^2) ≤ tensorCurvatureCouplingFormZero K F f := by
   have he : K=a • (1 : Matrix (Fin n) (Fin n) ℝ)+(K-a • (1 : Matrix (Fin n) (Fin n) ℝ)) := by abel
   rw [he,tensorCurvatureCouplingFormZero_add]
   have hbase : a*(∑ I, (F I)^2) ≤ tensorCurvatureCouplingFormZero (a • (1 : Matrix (Fin n) (Fin n) ℝ)) F f := by
     unfold tensorCurvatureCouplingFormZero
     rw [tensorPhysicalCurvatureForm_scalar_identity,tensorCurvatureCurlZero_scalar_identity a F hs,
       inner_zero_left,mul_zero,sub_zero]
     exact le_add_of_nonneg_right (tensorTwoFormCurvatureZero_scalar_nonneg ha f)
   exact hbase.trans (le_add_of_nonneg_right (tensorCurvatureCouplingFormZero_nonneg _
     (matrix_sub_scalar_identity_posSemidef K hK hlower) F f hf))

 theorem tensorCurvatureCurlZero_pairing_sub_correction_le (K : Matrix (Fin n) (Fin n) ℝ) (hK : K.IsSymm)
     (F : OrderedTensorIndex n 2 → ℝ)
     (hs : ∀ I J, List.Perm (List.ofFn I) (List.ofFn J) → F I=F J)
     (f : TensorTwoFormIndex n 0 → ℝ) (hf : ∀ I i j, f (I,i,j)= -f (I,j,i))
     {a : ℝ} (ha : 0 ≤ a)
     (hlower : ∀ v : Fin n → ℝ, a*(v ⬝ᵥ v) ≤ v ⬝ᵥ (K *ᵥ v)) :
     2*inner ℝ (tensorCurvatureCurlZero K F) (WithLp.toLp 2 f)-tensorTwoFormCurvatureZero K f ≤
       tensorPhysicalCurvatureForm K F-a*(∑ I, (F I)^2) := by
   have h := tensorCurvatureCouplingFormZero_lower K hK F hs f hf ha hlower
   unfold tensorCurvatureCouplingFormZero at h
   linarith

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.tensorCurvatureCouplingZero_rank_one_nonneg

#print axioms KLS.DeterministicBridgeIntegration.tensorCurvatureCouplingFormZero_nonneg
#print axioms KLS.DeterministicBridgeIntegration.tensorCurvatureCurlZero_pairing_sub_correction_le

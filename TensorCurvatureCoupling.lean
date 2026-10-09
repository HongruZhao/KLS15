import TensorPositiveCurvature

/-! Literal physical curvature/curl coupling for compact tensor estimate
(5.2). Positive rank-one matrices give actual completed norm squares;
there is no multiplicity-basis or presumed coupling inequality. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n r q : ℕ}

def tensorPhysicalCurvatureForm (K : Matrix (Fin n) (Fin n) ℝ)
    (F : OrderedTensorIndex n (q+1) → ℝ) : ℝ :=
  ∑ I : OrderedTensorIndex n q, ∑ i, ∑ j, K i j*F (Fin.cons i I)*F (Fin.cons j I)

def tensorCurvatureContraction (v : Fin n → ℝ)
    (F : OrderedTensorIndex n (r+3) → ℝ) :
    EuclideanSpace ℝ (TensorOneFormIndex n (r+1)) :=
  WithLp.toLp 2 (fun a => ∑ j, v j*F (Fin.cons j (Fin.cons a.2 a.1)))

def tensorCurvatureCurl (K : Matrix (Fin n) (Fin n) ℝ)
    (F : OrderedTensorIndex n (r+3) → ℝ) :
    EuclideanSpace ℝ (TensorTwoFormIndex n (r+1)) :=
  WithLp.toLp 2 (fun a => (1/Real.sqrt 2)*∑ j,
    (K a.2.1 j*F (Fin.cons j (Fin.cons a.2.2 a.1))-
      K a.2.2 j*F (Fin.cons j (Fin.cons a.2.1 a.1))))

lemma tensorCurvatureContraction_mem (v : Fin n → ℝ)
    (F : OrderedTensorIndex n (r+3) → ℝ)
    (hs : ∀ I J, List.Perm (List.ofFn I) (List.ofFn J) → F I=F J) :
    tensorCurvatureContraction v F ∈ tensorOneFormSymmetricFiber n (r+1) := by
  rw [mem_tensorOneFormSymmetricFiber_iff]
  intro a b hp
  change (∑ j, v j*F (Fin.cons j (Fin.cons a.2 a.1))) =
    ∑ j, v j*F (Fin.cons j (Fin.cons b.2 b.1))
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun t => v j*t)
  exact hs (Fin.cons j (Fin.cons a.2 a.1)) (Fin.cons j (Fin.cons b.2 b.1))
    (by simpa only [List.ofFn_cons] using List.Perm.cons j hp)

lemma tensorTwoFormCurvatureCorrection_rank_one_exact (v : Fin n → ℝ)
    (f : TensorTwoFormIndex n (r+1) → ℝ) (hf : TensorTwoFormCompatible f) :
    tensorTwoFormCurvatureCorrection (fun i j => v i*v j) f =
      2*‖tensorOneFormProjection n (r+1) (tensorTwoFormInterior v f)‖^2 := by
  have hp := Submodule.norm_sq_eq_add_norm_sq_starProjection (tensorTwoFormInterior v f)
    (tensorOneFormSymmetricFiber n (r+1))
  rw [Submodule.starProjection_orthogonal_val] at hp
  change ‖tensorTwoFormInterior v f‖^2 =
    ‖tensorOneFormProjection n (r+1) (tensorTwoFormInterior v f)‖^2+
      ‖tensorTwoFormInterior v f-tensorOneFormProjection n (r+1) (tensorTwoFormInterior v f)‖^2 at hp
  rw [tensorOneFormProjection_defect _ (tensorTwoFormInterior_auxiliarySymmetric v f hf)] at hp
  unfold tensorTwoFormCurvatureCorrection
  rw [tensorTwoFormExteriorCurvatureForm_rank_one,
    tensorTwoFormAuxiliaryCurvatureForm_rank_one v f hf]
  linarith

lemma tensorPhysicalCurvatureForm_rank_one (v : Fin n → ℝ)
    (F : OrderedTensorIndex n (r+3) → ℝ) :
    tensorPhysicalCurvatureForm (fun i j => v i*v j) F =
      ‖tensorCurvatureContraction v F‖^2 := by
  unfold tensorPhysicalCurvatureForm
  simp_rw [finite_rank_one_quadratic]
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs,sq_abs,tensorCurvatureContraction,PiLp.toLp_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  symm
  calc
    _ = ∑ p : Fin n × OrderedTensorIndex n (r+1),
      (∑ j, v j*F (Fin.cons j (Fin.cons p.1 p.2)))^2 := (Fintype.sum_prod_type _).symm
    _ = _ := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (r+2) => Fin n))
      _ _ (fun _ => rfl)

lemma finite_skew_pairing (v u : Fin n → ℝ) (f : Fin n → Fin n → ℝ)
    (hf : ∀ i j, f i j = -f j i) :
    (∑ i, ∑ j, (v i*u j-v j*u i)*f i j) =
      2*∑ j, u j*(∑ i, v i*f i j) := by
  have he : (∑ i, ∑ j, v j*u i*f i j) = -(∑ i, ∑ j, v i*u j*f i j) := by
    rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hf j i]
    ring
  simp only [sub_mul,Finset.sum_sub_distrib]
  rw [he]
  have hp : (∑ i, ∑ j, v i*u j*f i j) = ∑ j, u j*(∑ i, v i*f i j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hp]
  ring

lemma tensorCurvatureCurl_rank_one_apply (v : Fin n → ℝ)
    (F : OrderedTensorIndex n (r+3) → ℝ) (I : OrderedTensorIndex n (r+1)) (i j : Fin n) :
    tensorCurvatureCurl (fun i j => v i*v j) F (I,i,j) =
      (1/Real.sqrt 2)*(v i*tensorCurvatureContraction v F (I,j)-
        v j*tensorCurvatureContraction v F (I,i)) := by
  change (1/Real.sqrt 2)*(∑ k, ((v i*v k)*F (Fin.cons k (Fin.cons j I))-
    (v j*v k)*F (Fin.cons k (Fin.cons i I)))) = _
  simp only [Finset.sum_sub_distrib,tensorCurvatureContraction,PiLp.toLp_apply,
    Finset.mul_sum,mul_assoc]

lemma tensorCurvatureCurl_rank_one_pairing (v : Fin n → ℝ)
    (F : OrderedTensorIndex n (r+3) → ℝ)
    (f : TensorTwoFormIndex n (r+1) → ℝ) (hf : TensorTwoFormCompatible f) :
    inner ℝ (tensorCurvatureCurl (fun i j => v i*v j) F) (WithLp.toLp 2 f) =
      Real.sqrt 2*inner ℝ (tensorCurvatureContraction v F) (tensorTwoFormInterior v f) := by
  have he (I : OrderedTensorIndex n (r+1)) := finite_skew_pairing v
    (fun i => tensorCurvatureContraction v F (I,i)) (fun i j => f (I,i,j)) (hf.2.1 I)
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,Fintype.sum_prod_type,
    PiLp.toLp_apply]
  simp_rw [tensorCurvatureCurl_rank_one_apply]
  have hl : (∑ I : OrderedTensorIndex n (r+1), ∑ i, ∑ j,
      f (I,i,j)*((1/Real.sqrt 2)*(v i*tensorCurvatureContraction v F (I,j)-
        v j*tensorCurvatureContraction v F (I,i)))) =
      (1/Real.sqrt 2)*2*∑ I : OrderedTensorIndex n (r+1), ∑ j,
        tensorCurvatureContraction v F (I,j)*(∑ i, v i*f (I,i,j)) := by
    simp_rw [mul_left_comm (f _) (1/Real.sqrt 2), ← Finset.mul_sum]
    simp_rw [mul_comm (f _),he]
    simp only [← Finset.mul_sum,mul_assoc]
  rw [hl]
  have hs : (1/Real.sqrt 2)*2=Real.sqrt 2 := by
    calc
      _ = 2/Real.sqrt 2 := by ring
      _ = Real.sqrt 2 := (div_eq_iff (Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2))).2
        (by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)])
  rw [hs]
  congr 1
  simp only [tensorTwoFormInterior,PiLp.toLp_apply,mul_comm]

/-- Genuine pointwise completed square for a physical rank-one matrix. -/
theorem tensorCurvatureCoupling_rank_one_nonneg (v : Fin n → ℝ)
    (F : OrderedTensorIndex n (r+3) → ℝ)
    (hs : ∀ I J, List.Perm (List.ofFn I) (List.ofFn J) → F I=F J)
    (f : TensorTwoFormIndex n (r+1) → ℝ) (hf : TensorTwoFormCompatible f) :
    0 ≤ tensorPhysicalCurvatureForm (fun i j => v i*v j) F-
      2*inner ℝ (tensorCurvatureCurl (fun i j => v i*v j) F) (WithLp.toLp 2 f)+
        tensorTwoFormCurvatureCorrection (fun i j => v i*v j) f := by
  rw [tensorPhysicalCurvatureForm_rank_one,tensorCurvatureCurl_rank_one_pairing v F f hf,
    tensorTwoFormCurvatureCorrection_rank_one_exact v f hf]
  let T := tensorCurvatureContraction v F
  let w := tensorOneFormProjection n (r+1) (tensorTwoFormInterior v f)
  have hp : inner ℝ T (tensorTwoFormInterior v f)=inner ℝ T w := by
    have h := (tensorOneFormSymmetricFiber n (r+1)).starProjection_inner_eq_zero
      (tensorTwoFormInterior v f) T (tensorCurvatureContraction_mem v F hs)
    change inner ℝ (tensorTwoFormInterior v f-w) T=0 at h
    rw [inner_sub_left,real_inner_comm T (tensorTwoFormInterior v f),real_inner_comm T w] at h
    linarith
  change 0 ≤ ‖T‖^2-2*(Real.sqrt 2*inner ℝ T (tensorTwoFormInterior v f))+2*‖w‖^2
  rw [hp]
  have h := sq_nonneg ‖T-Real.sqrt 2 • w‖
  rw [norm_sub_sq_real,real_inner_smul_right,norm_smul,mul_pow,
    Real.norm_eq_abs,sq_abs,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)] at h
  nlinarith

def tensorCurvatureCouplingForm (K : Matrix (Fin n) (Fin n) ℝ)
    (F : OrderedTensorIndex n (r+3) → ℝ) (f : TensorTwoFormIndex n (r+1) → ℝ) : ℝ :=
  tensorPhysicalCurvatureForm K F-2*inner ℝ (tensorCurvatureCurl K F) (WithLp.toLp 2 f)+
    tensorTwoFormCurvatureCorrection K f

lemma tensorPhysicalCurvatureForm_add (K L : Matrix (Fin n) (Fin n) ℝ)
    (F : OrderedTensorIndex n (q+1) → ℝ) :
    tensorPhysicalCurvatureForm (K+L) F=
      tensorPhysicalCurvatureForm K F+tensorPhysicalCurvatureForm L F := by
  simp only [tensorPhysicalCurvatureForm,Matrix.add_apply,add_mul,Finset.sum_add_distrib]

lemma tensorCurvatureCurl_add (K L : Matrix (Fin n) (Fin n) ℝ)
    (F : OrderedTensorIndex n (r+3) → ℝ) :
    tensorCurvatureCurl (K+L) F=tensorCurvatureCurl K F+tensorCurvatureCurl L F := by
  apply PiLp.ext
  intro a
  change (1/Real.sqrt 2)*∑ j,
    ((K a.2.1 j+L a.2.1 j)*F (Fin.cons j (Fin.cons a.2.2 a.1))-
      (K a.2.2 j+L a.2.2 j)*F (Fin.cons j (Fin.cons a.2.1 a.1))) = _
  simp only [add_mul,Finset.sum_sub_distrib,Finset.sum_add_distrib,tensorCurvatureCurl,
    PiLp.toLp_apply,PiLp.add_apply]
  ring

lemma tensorCurvatureCouplingForm_add (K L : Matrix (Fin n) (Fin n) ℝ)
    (F : OrderedTensorIndex n (r+3) → ℝ) (f : TensorTwoFormIndex n (r+1) → ℝ) :
    tensorCurvatureCouplingForm (K+L) F f=
      tensorCurvatureCouplingForm K F f+tensorCurvatureCouplingForm L F f := by
  unfold tensorCurvatureCouplingForm
  rw [tensorPhysicalCurvatureForm_add,tensorCurvatureCurl_add,inner_add_left,
    tensorTwoFormCurvatureCorrection_add]
  ring

lemma tensorCurvatureCouplingForm_zero
    (F : OrderedTensorIndex n (r+3) → ℝ) (f : TensorTwoFormIndex n (r+1) → ℝ) :
    tensorCurvatureCouplingForm 0 F f=0 := by
  have hzero : tensorCurvatureCurl 0 F=0 := by
    apply PiLp.ext
    intro a
    simp [tensorCurvatureCurl]
  simp [tensorCurvatureCouplingForm,tensorPhysicalCurvatureForm,hzero,
    tensorTwoFormCurvatureCorrection_zero]

lemma tensorCurvatureCouplingForm_sum {τ : Type*} (s : Finset τ)
    (K : τ → Matrix (Fin n) (Fin n) ℝ)
    (F : OrderedTensorIndex n (r+3) → ℝ) (f : TensorTwoFormIndex n (r+1) → ℝ) :
    tensorCurvatureCouplingForm (∑ t ∈ s, K t) F f =
      ∑ t ∈ s, tensorCurvatureCouplingForm (K t) F f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tensorCurvatureCouplingForm_zero]
  | @insert t s ht ih =>
      rw [Finset.sum_insert ht,Finset.sum_insert ht,tensorCurvatureCouplingForm_add,ih]

/-- The physical completed square holds for every actual PSD matrix. -/
theorem tensorCurvatureCouplingForm_nonneg (K : Matrix (Fin n) (Fin n) ℝ) (hK : K.PosSemidef)
    (F : OrderedTensorIndex n (r+3) → ℝ)
    (hs : ∀ I J, List.Perm (List.ofFn I) (List.ofFn J) → F I=F J)
    (f : TensorTwoFormIndex n (r+1) → ℝ) (hf : TensorTwoFormCompatible f) :
    0 ≤ tensorCurvatureCouplingForm K F f := by
  obtain ⟨v,hv⟩ := positiveMatrix_row_gram K hK
  have he : K=∑ t : Fin n, (fun i j => v t i*v t j) := by
    ext i j
    simpa only [Finset.sum_apply] using hv i j
  rw [he,tensorCurvatureCouplingForm_sum]
  exact Finset.sum_nonneg (fun t _ => tensorCurvatureCoupling_rank_one_nonneg (v t) F hs f hf)

lemma tensorPhysicalCurvatureForm_scalar_identity (a : ℝ)
    (F : OrderedTensorIndex n (q+1) → ℝ) :
    tensorPhysicalCurvatureForm (a • (1 : Matrix (Fin n) (Fin n) ℝ)) F=
      a*∑ I, (F I)^2 := by
  unfold tensorPhysicalCurvatureForm
  simp only [Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,mul_ite,mul_one,mul_zero,
    ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  simp only [mul_assoc,←pow_two,←Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  calc
    _ = ∑ p : Fin n × OrderedTensorIndex n q, (F (Fin.cons p.1 p.2))^2 :=
      (Fintype.sum_prod_type _).symm
    _ = _ := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (q+1) => Fin n))
      _ _ (fun _ => rfl)

lemma tensorCurvatureCurl_scalar_identity (a : ℝ)
    (F : OrderedTensorIndex n (r+3) → ℝ)
    (hs : ∀ I J, List.Perm (List.ofFn I) (List.ofFn J) → F I=F J) :
    tensorCurvatureCurl (a • (1 : Matrix (Fin n) (Fin n) ℝ)) F=0 := by
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

/-- The exact physical pointwise coupling needed by (5.2). -/
theorem tensorCurvatureCouplingForm_lower
    (K : Matrix (Fin n) (Fin n) ℝ) (hK : K.IsSymm)
    (F : OrderedTensorIndex n (r+3) → ℝ)
    (hs : ∀ I J, List.Perm (List.ofFn I) (List.ofFn J) → F I=F J)
    (f : TensorTwoFormIndex n (r+1) → ℝ) (hf : TensorTwoFormCompatible f)
    {a : ℝ} (ha : 0 ≤ a)
    (hlower : ∀ v : Fin n → ℝ, a*(v ⬝ᵥ v) ≤ v ⬝ᵥ (K *ᵥ v)) :
    a*(∑ I, (F I)^2) ≤ tensorCurvatureCouplingForm K F f := by
  have he : K=a • (1 : Matrix (Fin n) (Fin n) ℝ)+
      (K-a • (1 : Matrix (Fin n) (Fin n) ℝ)) := by abel
  rw [he,tensorCurvatureCouplingForm_add]
  have hbase : a*(∑ I, (F I)^2) ≤
      tensorCurvatureCouplingForm (a • (1 : Matrix (Fin n) (Fin n) ℝ)) F f := by
    unfold tensorCurvatureCouplingForm
    rw [tensorPhysicalCurvatureForm_scalar_identity,tensorCurvatureCurl_scalar_identity a F hs,
      inner_zero_left,mul_zero,sub_zero,tensorTwoFormCurvatureCorrection_scalar_identity]
    exact le_add_of_nonneg_right (by unfold tensorTwoFormNormSq; positivity)
  exact hbase.trans (le_add_of_nonneg_right (tensorCurvatureCouplingForm_nonneg _
    (matrix_sub_scalar_identity_posSemidef K hK hlower) F hs f hf))

theorem tensorCurvatureCurl_pairing_sub_correction_le
    (K : Matrix (Fin n) (Fin n) ℝ) (hK : K.IsSymm)
    (F : OrderedTensorIndex n (r+3) → ℝ)
    (hs : ∀ I J, List.Perm (List.ofFn I) (List.ofFn J) → F I=F J)
    (f : TensorTwoFormIndex n (r+1) → ℝ) (hf : TensorTwoFormCompatible f)
    {a : ℝ} (ha : 0 ≤ a)
    (hlower : ∀ v : Fin n → ℝ, a*(v ⬝ᵥ v) ≤ v ⬝ᵥ (K *ᵥ v)) :
    2*inner ℝ (tensorCurvatureCurl K F) (WithLp.toLp 2 f)-
      tensorTwoFormCurvatureCorrection K f ≤
        tensorPhysicalCurvatureForm K F-a*(∑ I, (F I)^2) := by
  have h := tensorCurvatureCouplingForm_lower K hK F hs f hf ha hlower
  unfold tensorCurvatureCouplingForm at h
  linarith

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.tensorTwoFormCurvatureCorrection_rank_one_exact
#print axioms KLS.DeterministicBridgeIntegration.tensorPhysicalCurvatureForm_rank_one

#print axioms KLS.DeterministicBridgeIntegration.tensorCurvatureCoupling_rank_one_nonneg

#print axioms KLS.DeterministicBridgeIntegration.tensorCurvatureCouplingForm_nonneg

#print axioms KLS.DeterministicBridgeIntegration.tensorCurvatureCurl_pairing_sub_correction_le

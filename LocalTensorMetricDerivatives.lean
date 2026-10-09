import KLS.TensorMetricGenerator

/-! Local versions of the finite tensor metric derivative identities. Only
actual germs near the evaluation point are used; no global matrix-field
invertibility or global smooth extension is imposed. -/
noncomputable section
open Matrix Filter Set
open scoped BigOperators Matrix.Norms.Elementwise Topology
namespace KLS.DeterministicBridgeNext
open KLS.TensorEnergy KLS.MatrixCalculus
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

 theorem eventually_differentiableAt_of_contDiffAt {f : E → F} {x : E}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) :
    ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y := by
  have h1 : ContDiffAt ℝ 1 f x := hf.of_le (by simp)
  filter_upwards [h1.eventually (by norm_num)] with y hy
  exact hy.differentiableAt (by simp)

 theorem differentiableAt_directional_of_contDiffAt {f : E → F} {x : E}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (v : E) :
    DifferentiableAt ℝ (fun y => fderiv ℝ f y v) x :=
  ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp)).clm_apply
    (differentiableAt_const v)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem local_fderiv_fderiv_matrix_inv_apply {A : E → Matrix ι ι ℝ} {x : E}
    (hA : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ A y) (v w : E)
    (hAv : DifferentiableAt ℝ (fun y => fderiv ℝ A y v) x) (hdet : (A x).det ≠ 0) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => (A z)⁻¹) y v) x w =
      (A x)⁻¹ * fderiv ℝ A x w * (A x)⁻¹ * fderiv ℝ A x v * (A x)⁻¹ +
      (A x)⁻¹ * fderiv ℝ A x v * (A x)⁻¹ * fderiv ℝ A x w * (A x)⁻¹ -
      (A x)⁻¹ * fderiv ℝ (fun y => fderiv ℝ A y v) x w * (A x)⁻¹ := by
  have hInv : DifferentiableAt ℝ (fun y => (A y)⁻¹) x :=
    (differentiableAt_matrix_inv (A x) hdet).comp x hA.self_of_nhds
  have heq : (fun y => fderiv ℝ (fun z => (A z)⁻¹) y v) =ᶠ[𝓝 x]
      fun y => -((A y)⁻¹ * fderiv ℝ A y v * (A y)⁻¹) := by
    have hn : ∀ᶠ y in 𝓝 x, (A y).det ≠ 0 :=
      (contDiff_det.continuous.continuousAt.comp hA.self_of_nhds.continuousAt).eventually_ne hdet
    filter_upwards [hn,hA] with y hy hAy
    exact fderiv_matrix_inv_comp_apply hAy hy v
  have hProd := differentiableAt_matrix_mul hInv hAv
  rw [heq.fderiv_eq, fderiv_fun_neg]
  simp only [ContinuousLinearMap.neg_apply]
  rw [fderiv_matrix_mul_apply hProd hInv, fderiv_matrix_mul_apply hInv hAv,
    fderiv_matrix_inv_comp_apply hA.self_of_nhds hdet]
  noncomm_ring

/-- Identity-point specialization with arbitrary first and second derivatives. -/
theorem local_fderiv_fderiv_matrix_inv_at_identity {A : E → Matrix ι ι ℝ} {x : E}
    (hA : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ A y) (v : E)
    (hAv : DifferentiableAt ℝ (fun y => fderiv ℝ A y v) x) (hI : A x = 1) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => (A z)⁻¹) y v) x v =
      2 • (fderiv ℝ A x v * fderiv ℝ A x v) -
      fderiv ℝ (fun y => fderiv ℝ A y v) x v := by
  have hdet : (A x).det ≠ 0 := by simp [hI]
  rw [local_fderiv_fderiv_matrix_inv_apply hA v v hAv hdet, hI]
  simp [two_smul]


theorem local_fderiv_fderiv_tensorMatrixFamily_identity
    {A : E → Fin r → Matrix (Fin n) (Fin n) ℝ} {x : E}
    (hA : ∀ᶠ y in 𝓝 x, ∀ j, DifferentiableAt ℝ (fun z => A z j) y) (v w : E)
    (hAv : ∀ j, DifferentiableAt ℝ (fun y => fderiv ℝ (fun z => A z j) y v) x)
    (hI : ∀ j, A x j = 1) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => tensorMatrixFamily (A z)) y v) x w =
      ∑ s, (tensorSlot s (fderiv ℝ (fun y => fderiv ℝ (fun z => A z s) y v) x w) +
        ∑ t ∈ Finset.univ.erase s,
          tensorSlot s (fderiv ℝ (fun y => A y s) x v) *
          tensorSlot t (fderiv ℝ (fun y => A y t) x w)) := by
  have hEq : (fun y => fderiv ℝ (fun z => tensorMatrixFamily (A z)) y v) =ᶠ[𝓝 x]
      fun y => ∑ s, tensorMatrixFamily (Function.update (A y) s (fderiv ℝ (fun z => A z s) y v)) := by
    filter_upwards [hA] with y hy
    exact fderiv_tensorMatrixFamily_apply hy v
  rw [hEq.fderiv_eq]
  have hEach : ∀ s : Fin r,
      DifferentiableAt ℝ (fun y => tensorMatrixFamily (Function.update (A y) s (fderiv ℝ (fun z => A z s) y v))) x := by
    intro s
    apply differentiableAt_tensorMatrixFamily
    intro j
    by_cases hjs : j=s
    · subst j
      simpa only [Function.update_self] using hAv s
    · simpa only [Function.update_of_ne hjs] using hA.self_of_nhds j
  rw [fderiv_fun_sum (u := Finset.univ) (fun s _ => hEach s)]
  simp only [_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro s _
  exact fderiv_tensorMatrixFamily_update_identity (fun j => hA.self_of_nhds j) (hAv s) hI s w


theorem local_differentiableAt_inverse_directional_derivative
    {A : E → Matrix (Fin n) (Fin n) ℝ} {x : E}
    (hA : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ A y) (hdet : (A x).det ≠ 0) (v : E)
    (hAv : DifferentiableAt ℝ (fun y => fderiv ℝ A y v) x) :
    DifferentiableAt ℝ (fun y => fderiv ℝ (fun z => (A z)⁻¹) y v) x := by
  have hEq : (fun y => fderiv ℝ (fun z => (A z)⁻¹) y v) =ᶠ[𝓝 x]
      fun y => -((A y)⁻¹ * fderiv ℝ A y v * (A y)⁻¹) := by
    have hn : ∀ᶠ y in 𝓝 x, (A y).det ≠ 0 :=
      (contDiff_det.continuous.continuousAt.comp hA.self_of_nhds.continuousAt).eventually_ne hdet
    filter_upwards [hn,hA] with y hy hAy
    exact fderiv_matrix_inv_comp_apply hAy hy v
  apply DifferentiableAt.congr_of_eventuallyEq (f := fun y => -((A y)⁻¹ * fderiv ℝ A y v * (A y)⁻¹)) _ hEq
  have hInv : DifferentiableAt ℝ (fun y => (A y)⁻¹) x :=
    (differentiableAt_matrix_inv (A x) hdet).comp x hA.self_of_nhds
  exact (differentiableAt_matrix_mul (differentiableAt_matrix_mul hInv hAv) hInv).neg

theorem local_fderiv_fderiv_tensorInverse_at_identity
    {A : E → Matrix (Fin n) (Fin n) ℝ} {x : E}
    (hA : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ A y) (hdet : (A x).det ≠ 0) (v : E)
    (hAv : DifferentiableAt ℝ (fun y => fderiv ℝ A y v) x) (hI : A x = 1) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => tensorMatrix (r := r) (A z)⁻¹) y v) x v =
      tensorSlotSum (fderiv ℝ A x v) * tensorSlotSum (fderiv ℝ A x v) +
      ∑ s, tensorSlot s (fderiv ℝ A x v) * tensorSlot s (fderiv ℝ A x v) -
      tensorSlotSum (fderiv ℝ (fun y => fderiv ℝ A y v) x v) := by
  have hn : ∀ᶠ y in 𝓝 x, (A y).det ≠ 0 :=
    (contDiff_det.continuous.continuousAt.comp hA.self_of_nhds.continuousAt).eventually_ne hdet
  have hInv : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun z => (A z)⁻¹) y := by
    filter_upwards [hA,hn] with y hy hdy
    exact (differentiableAt_matrix_inv (A y) hdy).comp y hy
  have hInvv := local_differentiableAt_inverse_directional_derivative hA hdet v hAv
  change fderiv ℝ (fun y => fderiv ℝ (fun z => tensorMatrixFamily (fun _ : Fin r => (A z)⁻¹)) y v) x v = _
  rw [local_fderiv_fderiv_tensorMatrixFamily_identity (hInv.mono (fun y hy _ => hy)) v v (fun _ => hInvv) (fun _ => by simp [hI])]
  simp only [local_fderiv_fderiv_matrix_inv_at_identity hA v hAv hI,
    fderiv_matrix_inv_comp_apply hA.self_of_nhds hdet, hI, inv_one,
    Matrix.one_mul, Matrix.mul_one, tensorSlot_sub, tensorSlot_neg, neg_mul_neg,
    two_smul, tensorSlot_add, tensorSlot_mul]
  simp_rw [sub_add_eq_add_sub]
  rw [Finset.sum_sub_distrib, sum_twice_diagonal_add_offdiagonal]
  rfl


theorem local_fderiv_fderiv_quadratic_at_identity
    {Q : E → Matrix ι ι ℝ} {T : E → ι → ℝ} {x : E}
    (hQ : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ Q y)
    (hT : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ T y) (v : E)
    (hQv : DifferentiableAt ℝ (fun y => fderiv ℝ Q y v) x)
    (hTv : DifferentiableAt ℝ (fun y => fderiv ℝ T y v) x)
    (hI : Q x = 1) (hS : (fderiv ℝ Q x v).transpose = fderiv ℝ Q x v) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => T z ⬝ᵥ (Q z *ᵥ T z)) y v) x v =
      2 * (T x ⬝ᵥ fderiv ℝ (fun y => fderiv ℝ T y v) x v) +
      2 * (fderiv ℝ T x v ⬝ᵥ fderiv ℝ T x v) +
      4 * (fderiv ℝ T x v ⬝ᵥ (fderiv ℝ Q x v *ᵥ T x)) +
      T x ⬝ᵥ (fderiv ℝ (fun y => fderiv ℝ Q y v) x v *ᵥ T x) := by
  have heq : (fun y => fderiv ℝ (fun z => T z ⬝ᵥ (Q z *ᵥ T z)) y v) =ᶠ[𝓝 x]
      fun y => fderiv ℝ T y v ⬝ᵥ (Q y *ᵥ T y) +
        T y ⬝ᵥ (fderiv ℝ Q y v *ᵥ T y + Q y *ᵥ fderiv ℝ T y v) := by
    filter_upwards [hQ,hT] with y hQy hTy
    exact fderiv_quadratic_apply hQy hTy v
  rw [heq.fderiv_eq]
  have hQT := differentiableAt_mulVec hQ.self_of_nhds hT.self_of_nhds
  have hQvT := differentiableAt_mulVec hQv hT.self_of_nhds
  have hQTv := differentiableAt_mulVec hQ.self_of_nhds hTv
  have hSum : DifferentiableAt ℝ
      (fun y => fderiv ℝ Q y v *ᵥ T y + Q y *ᵥ fderiv ℝ T y v) x := hQvT.add hQTv
  rw [fderiv_fun_add (differentiableAt_dotProduct hTv hQT)
    (differentiableAt_dotProduct hT.self_of_nhds hSum)]
  simp only [_root_.add_apply]
  rw [fderiv_dotProduct_apply hTv hQT v,
    fderiv_dotProduct_apply hT.self_of_nhds hSum v,
    fderiv_fun_add hQvT hQTv]
  simp only [_root_.add_apply]
  rw [fderiv_mulVec_apply hQ.self_of_nhds hT.self_of_nhds v,
    fderiv_mulVec_apply hQv hT.self_of_nhds v, fderiv_mulVec_apply hQ.self_of_nhds hTv v, hI]
  simp only [Matrix.one_mulVec, dotProduct_add]
  have hSym : T x ⬝ᵥ (fderiv ℝ Q x v *ᵥ fderiv ℝ T x v) =
      fderiv ℝ T x v ⬝ᵥ (fderiv ℝ Q x v *ᵥ T x) := by
    rw [← hS, Matrix.dotProduct_transpose_mulVec, hS]
  rw [hSym, dotProduct_comm (fderiv ℝ (fun y => fderiv ℝ T y v) x v) (T x)]
  ring


 theorem contDiffAt_matrixInverse {A : E → Matrix (Fin n) (Fin n) ℝ} {x : E}
    (hA : ContDiffAt ℝ (⊤ : ℕ∞) A x) (hdet : (A x).det ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (A y)⁻¹) x := by
  have hdetSmooth : ContDiffAt ℝ (⊤ : ℕ∞) Matrix.det (A x) :=
    contDiff_det.contDiffAt.of_le (by simp)
  have hd : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (A y).det) x :=
    hdetSmooth.comp x hA
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  have hadj : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => (A y).adjugate i j) x := by
    simp_rw [Matrix.adjugate_apply,Matrix.det_apply']
    apply ContDiffAt.sum
    intro σ _
    apply contDiffAt_const.mul
    apply contDiffAt_prod
    intro a _
    by_cases ha : σ a = j
    · simp only [ha,Matrix.updateRow_self]
      exact contDiffAt_const
    · simp only [Matrix.updateRow_ne ha]
      exact contDiffAt_pi.mp (contDiffAt_pi.mp hA (σ a)) a
  simp_rw [Matrix.inv_def,Matrix.smul_apply,smul_eq_mul,Ring.inverse_eq_inv]
  exact (hd.inv hdet).mul hadj

 theorem contDiffAt_tensorInverse {A : E → Matrix (Fin n) (Fin n) ℝ} {x : E}
    (hA : ContDiffAt ℝ (⊤ : ℕ∞) A x) (hdet : (A x).det ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => tensorMatrix (r := r) (A y)⁻¹) x := by
  have hInv := contDiffAt_matrixInverse hA hdet
  apply contDiffAt_pi.mpr
  intro a
  apply contDiffAt_pi.mpr
  intro b
  change ContDiffAt ℝ (⊤ : ℕ∞) (fun y => ∏ j : Fin r, (A y)⁻¹ (a j) (b j)) x
  exact contDiffAt_prod (fun j _ =>
    contDiffAt_pi.mp (contDiffAt_pi.mp hInv (a j)) (b j))

 theorem contDiffAt_tensorMetric {A : E → Matrix (Fin n) (Fin n) ℝ}
    {T : E → (Fin r → Fin n) → ℝ} {x : E}
    (hA : ContDiffAt ℝ (⊤ : ℕ∞) A x) (hdet : (A x).det ≠ 0)
    (hT : ContDiffAt ℝ (⊤ : ℕ∞) T x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => tensorMetric (A y) (T y)) x := by
  have hQ := contDiffAt_tensorInverse (r := r) hA hdet
  unfold tensorMetric Matrix.mulVec dotProduct
  apply ContDiffAt.sum
  intro a _
  apply (contDiffAt_pi.mp hT a).mul
  apply ContDiffAt.sum
  intro b _
  exact (contDiffAt_pi.mp (contDiffAt_pi.mp hQ a) b).mul (contDiffAt_pi.mp hT b)

 theorem local_fderiv_tensorMetric_at_identity
    {A : E → Matrix (Fin n) (Fin n) ℝ} {T : E → (Fin r → Fin n) → ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hT : DifferentiableAt ℝ T x)
    (hI : A x = 1) (v : E) :
    fderiv ℝ (fun y => tensorMetric (A y) (T y)) x v =
      2 * (T x ⬝ᵥ fderiv ℝ T x v) -
        T x ⬝ᵥ (tensorSlotSum (fderiv ℝ A x v) *ᵥ T x) := by
  have hdet : (A x).det ≠ 0 := by simp [hI]
  have hInv : DifferentiableAt ℝ (fun y => (A y)⁻¹) x :=
    (differentiableAt_matrix_inv (A x) hdet).comp x hA
  have hQ : DifferentiableAt ℝ (fun y => tensorMatrix (r := r) (A y)⁻¹) x :=
    differentiableAt_tensorMatrixFamily (fun _ => hInv)
  unfold tensorMetric
  rw [fderiv_quadratic_at_identity hQ hT (by simp [hI,tensorMatrix_one]) v,
    fderiv_tensorInverse_at_identity hA hI v]
  simp [Matrix.neg_mulVec,sub_eq_add_neg]

 theorem local_fderiv_fderiv_tensorMetric_at_identity
    {A : E → Matrix (Fin n) (Fin n) ℝ} {T : E → (Fin r → Fin n) → ℝ} {x : E}
    (hA : ContDiffAt ℝ (⊤ : ℕ∞) A x) (hT : ContDiffAt ℝ (⊤ : ℕ∞) T x)
    (hI : A x = 1) (v : E)
    (hH : (fderiv ℝ A x v).transpose = fderiv ℝ A x v) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => tensorMetric (A z) (T z)) y v) x v =
      2 * (T x ⬝ᵥ fderiv ℝ (fun y => fderiv ℝ T y v) x v) -
      T x ⬝ᵥ (tensorSlotSum (fderiv ℝ (fun y => fderiv ℝ A y v) x v) *ᵥ T x) +
      2 * (fderiv ℝ T x v ⬝ᵥ fderiv ℝ T x v) -
      4 * (fderiv ℝ T x v ⬝ᵥ (tensorSlotSum (fderiv ℝ A x v) *ᵥ T x)) +
      (tensorSlotSum (fderiv ℝ A x v) *ᵥ T x) ⬝ᵥ (tensorSlotSum (fderiv ℝ A x v) *ᵥ T x) +
      ∑ s, (tensorSlot s (fderiv ℝ A x v) *ᵥ T x) ⬝ᵥ (tensorSlot s (fderiv ℝ A x v) *ᵥ T x) := by
  have hdet : (A x).det ≠ 0 := by simp [hI]
  have hQ := contDiffAt_tensorInverse (r := r) hA hdet
  have hAd := eventually_differentiableAt_of_contDiffAt hA
  have hAv := differentiableAt_directional_of_contDiffAt hA v
  have hQv := differentiableAt_directional_of_contDiffAt hQ v
  have hTv := differentiableAt_directional_of_contDiffAt hT v
  have hQI : tensorMatrix (r := r) (A x)⁻¹ = 1 := by simp [hI,tensorMatrix_one]
  have hQS : (fderiv ℝ (fun y => tensorMatrix (r := r) (A y)⁻¹) x v).transpose =
      fderiv ℝ (fun y => tensorMatrix (r := r) (A y)⁻¹) x v := by
    rw [fderiv_tensorInverse_at_identity hAd.self_of_nhds hI v]
    simp only [Matrix.transpose_neg,tensorSlotSum_transpose,hH]
  unfold tensorMetric
  rw [local_fderiv_fderiv_quadratic_at_identity
    (eventually_differentiableAt_of_contDiffAt hQ)
    (eventually_differentiableAt_of_contDiffAt hT) v hQv hTv hQI hQS,
    fderiv_tensorInverse_at_identity hAd.self_of_nhds hI v,
    local_fderiv_fderiv_tensorInverse_at_identity hAd hdet v hAv hI]
  simp only [Matrix.neg_mulVec,dotProduct_neg,Matrix.sub_mulVec,Matrix.add_mulVec,
    dotProduct_add,dotProduct_sub,Matrix.sum_mulVec,dotProduct_sum]
  rw [dotProduct_matrix_square _ (by rw [tensorSlotSum_transpose,hH])]
  have hs (s : Fin r) := dotProduct_matrix_square (tensorSlot s (fderiv ℝ A x v))
    (by rw [tensorSlot_transpose,hH]) (T x)
  simp_rw [hs]
  ring

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.local_fderiv_fderiv_tensorMetric_at_identity
#print axioms KLS.DeterministicBridgeNext.contDiffAt_tensorMetric

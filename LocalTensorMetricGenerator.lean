import LocalTensorMetricDerivatives

/-! The actual one-sided damping / two-sided tilt generator. The metric
identity is local in tilt and uses genuine right damping derivatives. -/
noncomputable section
open Matrix Filter Set
open scoped BigOperators Matrix.Norms.Elementwise Topology
namespace KLS.DeterministicBridgeNext
open KLS.TensorEnergy KLS.MatrixCalculus
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n r q : ℕ}
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

 def localHeatGenerator (σ : Fin q → E) (f : ℝ → E → F) : F :=
  derivWithin (fun s => f s 0) (Ici 0) 0 +
    (1/2 : ℝ) • ∑ k, fderiv ℝ (fun y => fderiv ℝ (f 0) y (σ k)) 0 (σ k)

 theorem localHeatGenerator_compCLM
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) {f : ℝ → E → F}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) (f 0) 0)
    (hfs : DifferentiableWithinAt ℝ (fun s => f s 0) (Ici 0) 0)
    (σ : Fin q → E) :
    localHeatGenerator σ (fun s y => L (f s y)) = L (localHeatGenerator σ f) := by
  unfold localHeatGenerator
  dsimp only
  have hsd := (L.hasFDerivAt.comp_hasDerivWithinAt (0 : ℝ) hfs.hasDerivWithinAt).derivWithin
    (uniqueDiffWithinAt_Ici (0 : ℝ))
  simp only [Function.comp_def] at hsd
  rw [hsd]
  have he (v : E) : (fun y => fderiv ℝ (fun z => L (f 0 z)) y v) =ᶠ[𝓝 (0 : E)]
      (fun y => L (fderiv ℝ (f 0) y v)) := by
    filter_upwards [eventually_differentiableAt_of_contDiffAt hf] with y hy
    exact fderiv_compCLM_apply L hy v
  simp_rw [(he _).fderiv_eq]
  simp_rw [fderiv_compCLM_apply L (differentiableAt_directional_of_contDiffAt hf _) _]
  simp only [map_add,map_smul,map_sum]


 theorem hasDerivWithinAt_tensorMetric_at_identity
    {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {T : ℝ → (Fin r → Fin n) → ℝ}
    {A' : Matrix (Fin n) (Fin n) ℝ} {T' : (Fin r → Fin n) → ℝ}
    (hA : HasDerivWithinAt A A' (Ici 0) 0) (hT : HasDerivWithinAt T T' (Ici 0) 0)
    (hI : A 0 = 1) :
    HasDerivWithinAt (fun s => tensorMetric (A s) (T s))
      (2*(T 0 ⬝ᵥ T')-T 0 ⬝ᵥ (tensorSlotSum A' *ᵥ T 0)) (Ici 0) 0 := by
  let M := Matrix (Fin n) (Fin n) ℝ
  let V := (Fin r → Fin n) → ℝ
  let p : M × V := (A 0,T 0)
  let m : M × V → ℝ := fun p => tensorMetric p.1 p.2
  have hfst : ContDiffAt ℝ (⊤ : ℕ∞) (Prod.fst : M × V → M) p := contDiffAt_fst
  have hsnd : ContDiffAt ℝ (⊤ : ℕ∞) (Prod.snd : M × V → V) p := contDiffAt_snd
  have hdet : p.1.det ≠ 0 := by dsimp [p]; simp [hI]
  have hm : DifferentiableAt ℝ m p :=
    (contDiffAt_tensorMetric hfst hdet hsnd).differentiableAt (by simp)
  have he : fderiv ℝ m p (A',T') =
      2*(T 0 ⬝ᵥ T')-T 0 ⬝ᵥ (tensorSlotSum A' *ᵥ T 0) := by
    change fderiv ℝ (fun p : M × V => tensorMetric p.1 p.2) p (A',T') = _
    rw [local_fderiv_tensorMetric_at_identity (hfst.differentiableAt (by simp))
      (hsnd.differentiableAt (by simp)) (by simpa [p] using hI) (A',T')]
    rw [fderiv_snd, fderiv_fst]
    rfl
  have hc := hm.hasFDerivAt.comp_hasDerivWithinAt (0 : ℝ) (hA.prodMk hT)
  rw [he] at hc
  exact hc

 theorem localHeatGenerator_tensorMetric_at_identity
    {A : ℝ → E → Matrix (Fin n) (Fin n) ℝ}
    {T : ℝ → E → (Fin r → Fin n) → ℝ}
    (hA : ContDiffAt ℝ (⊤ : ℕ∞) (A 0) 0)
    (hT : ContDiffAt ℝ (⊤ : ℕ∞) (T 0) 0)
    (hAs : DifferentiableWithinAt ℝ (fun s => A s 0) (Ici 0) 0)
    (hTs : DifferentiableWithinAt ℝ (fun s => T s 0) (Ici 0) 0)
    (σ : Fin q → E) (hI : A 0 0 = 1)
    (hH : ∀ k, (fderiv ℝ (A 0) 0 (σ k)).transpose = fderiv ℝ (A 0) 0 (σ k)) :
    localHeatGenerator σ (fun s y => tensorMetric (A s y) (T s y)) =
      2*(T 0 0 ⬝ᵥ localHeatGenerator σ T)-
      T 0 0 ⬝ᵥ (tensorSlotSum (localHeatGenerator σ A) *ᵥ T 0 0)+
      ∑ k, (fderiv ℝ (T 0) 0 (σ k) ⬝ᵥ fderiv ℝ (T 0) 0 (σ k)-
        2*(fderiv ℝ (T 0) 0 (σ k) ⬝ᵥ
          (tensorSlotSum (fderiv ℝ (A 0) 0 (σ k)) *ᵥ T 0 0))+
        (1/2 : ℝ)*((tensorSlotSum (fderiv ℝ (A 0) 0 (σ k)) *ᵥ T 0 0) ⬝ᵥ
          (tensorSlotSum (fderiv ℝ (A 0) 0 (σ k)) *ᵥ T 0 0))+
        (1/2 : ℝ)*∑ s, ((tensorSlot s (fderiv ℝ (A 0) 0 (σ k)) *ᵥ T 0 0) ⬝ᵥ
          (tensorSlot s (fderiv ℝ (A 0) 0 (σ k)) *ᵥ T 0 0))) := by
  unfold localHeatGenerator
  rw [(hasDerivWithinAt_tensorMetric_at_identity hAs.hasDerivWithinAt
    hTs.hasDerivWithinAt hI).derivWithin (uniqueDiffWithinAt_Ici (0 : ℝ))]
  simp_rw [local_fderiv_fderiv_tensorMetric_at_identity hA hT hI _ (hH _)]
  rw [tensorSlotSum_add,tensorSlotSum_smul]
  have hSum (M : Fin q → Matrix (Fin n) (Fin n) ℝ) :
      tensorSlotSum (r := r) (∑ k, M k) = ∑ k, tensorSlotSum (M k) :=
    map_sum (tensorSlotSumCLM (r := r)) M Finset.univ
  rw [hSum]
  simp only [smul_eq_mul,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.sum_mulVec,
    dotProduct_add,dotProduct_smul,dotProduct_sum,Finset.sum_add_distrib,
    Finset.sum_sub_distrib,← Finset.mul_sum]
  ring

 theorem localHeatGenerator_tensorMetric_with_drift
    {A : ℝ → E → Matrix (Fin n) (Fin n) ℝ}
    {T : ℝ → E → (Fin r → Fin n) → ℝ}
    (hA : ContDiffAt ℝ (⊤ : ℕ∞) (A 0) 0)
    (hT : ContDiffAt ℝ (⊤ : ℕ∞) (T 0) 0)
    (hAs : DifferentiableWithinAt ℝ (fun s => A s 0) (Ici 0) 0)
    (hTs : DifferentiableWithinAt ℝ (fun s => T s 0) (Ici 0) 0)
    (σ : Fin q → E) (hI : A 0 0 = 1)
    (hH : ∀ k, (fderiv ℝ (A 0) 0 (σ k)).transpose = fderiv ℝ (A 0) 0 (σ k))
    (m : ℝ) (L : (Fin r → Fin n) → ℝ)
    (hGA : localHeatGenerator σ A = -1)
    (hGT : localHeatGenerator σ T = -(m • T 0 0+L)) :
    localHeatGenerator σ (fun s y => tensorMetric (A s y) (T s y)) =
      (r-2*m)*(T 0 0 ⬝ᵥ T 0 0)-2*(T 0 0 ⬝ᵥ L)+
      ∑ k, (fderiv ℝ (T 0) 0 (σ k) ⬝ᵥ fderiv ℝ (T 0) 0 (σ k)-
        2*(fderiv ℝ (T 0) 0 (σ k) ⬝ᵥ
          (tensorSlotSum (fderiv ℝ (A 0) 0 (σ k)) *ᵥ T 0 0))+
        (1/2 : ℝ)*((tensorSlotSum (fderiv ℝ (A 0) 0 (σ k)) *ᵥ T 0 0) ⬝ᵥ
          (tensorSlotSum (fderiv ℝ (A 0) 0 (σ k)) *ᵥ T 0 0))+
        (1/2 : ℝ)*∑ s, ((tensorSlot s (fderiv ℝ (A 0) 0 (σ k)) *ᵥ T 0 0) ⬝ᵥ
          (tensorSlot s (fderiv ℝ (A 0) 0 (σ k)) *ᵥ T 0 0))) := by
  rw [localHeatGenerator_tensorMetric_at_identity hA hT hAs hTs σ hI hH,hGA,hGT,
    tensorSlotSum_neg,tensorSlotSum_one]
  simp only [dotProduct_neg,dotProduct_add,dotProduct_smul,Matrix.neg_mulVec,
    Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul,Nat.cast_smul_eq_nsmul ℝ]
  push_cast
  ring

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.hasDerivWithinAt_tensorMetric_at_identity
#print axioms KLS.DeterministicBridgeNext.localHeatGenerator_tensorMetric_with_drift

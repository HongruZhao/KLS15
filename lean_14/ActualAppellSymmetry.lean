import ActualLawTiltSmooth
import AppellNoiseCorrection
import KLS.DirectionalWordSymmetry

/-! Local mixed-derivative symmetry and its actual-law Appell tensor
consequences. The local C∞ premise is proved from log-concavity and L². -/
noncomputable section
open MeasureTheory Set Filter Matrix Metric
open scoped ContDiff Topology BigOperators
namespace KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
section LocalSymmetry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {U : Set E} {f : E → ℝ}

 theorem contDiffOn_word_of_isOpen (hU : IsOpen U)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (vs : List E) :
    ContDiffOn ℝ (⊤ : ℕ∞) (directionalWordDerivative f vs) U := by
  induction vs with
  | nil => exact hf
  | cons v vs ih => exact (ih.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

 theorem local_word_swap (hU : IsOpen U)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (a b : E) (vs : List E) :
    EqOn (directionalWordDerivative f (a::b::vs))
      (directionalWordDerivative f (b::a::vs)) U := by
  intro x hx
  let g := directionalWordDerivative f vs
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) g U := contDiffOn_word_of_isOpen hU hf vs
  have hga := hg.contDiffAt (hU.mem_nhds hx)
  have hgd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    ((hg.fderiv_of_isOpen hU (m:=(1:ℕ∞ω)) (by simp)).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  change fderiv ℝ (fun y => fderiv ℝ g y b) x a =
    fderiv ℝ (fun y => fderiv ℝ g y a) x b
  rw [fderiv_clm_apply hgd (differentiableAt_const _),
    fderiv_clm_apply hgd (differentiableAt_const _)]
  simpa using hga.isSymmSndFDerivAt (by norm_num) |>.eq a b

 theorem local_word_perm (hU : IsOpen U)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) {vs ws : List E} (hp : vs.Perm ws) :
    EqOn (directionalWordDerivative f vs) (directionalWordDerivative f ws) U := by
  induction hp with
  | nil => exact fun _ _ => rfl
  | @cons a l₁ l₂ hp ih =>
      intro x hx
      have he : directionalWordDerivative f l₁ =ᶠ[𝓝 x] directionalWordDerivative f l₂ :=
        by
          filter_upwards [hU.mem_nhds hx] with y hy
          exact ih hy
      change fderiv ℝ _ x a = fderiv ℝ _ x a
      rw [he.fderiv_eq]
  | swap a b vs => exact local_word_swap hU hf b a vs
  | trans hp hq ihp ihq => exact fun x hx => (ihp hx).trans (ihq hx)

 theorem local_word_ofFn (hU : IsOpen U)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) {k : ℕ} (m : Fin k → E) :
    EqOn (directionalWordDerivative f (List.ofFn m))
      (fun x => iteratedFDeriv ℝ k f x m) U := by
  induction k with
  | zero => intro x hx; simp [iteratedFDeriv_zero_apply]
  | succ k ih =>
      intro x hx
      rw [List.ofFn_succ]
      change fderiv ℝ (directionalWordDerivative f (List.ofFn (Fin.tail m))) x (m 0) = _
      have he : directionalWordDerivative f (List.ofFn (Fin.tail m)) =ᶠ[𝓝 x]
          (fun y => iteratedFDeriv ℝ k f y (Fin.tail m)) :=
        by
          filter_upwards [hU.mem_nhds hx] with y hy
          exact ih (Fin.tail m) hy
      rw [he.fderiv_eq]
      have hd := (((hf.contDiffAt (hU.mem_nhds hx)).iteratedFDeriv_right
        (i:=k) (m:=(1:ℕ∞ω)) (by simp)).differentiableAt (by norm_num))
      exact (hd.iteratedFDeriv_succ_apply_left' (m:=m)).symm

 theorem local_iteratedFDeriv_comp_perm (hU : IsOpen U)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) {k : ℕ} (m : Fin k → E)
    (σ : Equiv.Perm (Fin k)) {x : E} (hx : x ∈ U) :
    iteratedFDeriv ℝ k f x (m ∘ σ) = iteratedFDeriv ℝ k f x m := by
  exact (local_word_ofFn hU hf (m ∘ σ) hx).symm.trans
    ((local_word_perm hU hf (σ.ofFn_comp_perm m) hx).trans
      (local_word_ofFn hU hf m hx))
end LocalSymmetry

variable {n r : ℕ}

/-- Appell coefficient symmetry for the entire original actual law class. -/
theorem actualAppellCoefficient_symmetric
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    CoordinateTensorSymmetric (actualAppellCoefficient μ f r) := by
  obtain ⟨b,hb,hs⟩ := exists_ball_contDiffOn_normalized_tilt_average hμ hf
  intro s t a
  unfold actualAppellCoefficient
  simpa only [Function.comp_def] using local_iteratedFDeriv_comp_perm isOpen_ball hs
    (fun j => EuclideanSpace.single (a j) 1) (Equiv.swap s t)
    (by simpa using hb : (0 : Space n) ∈ Metric.ball 0 b)

/-- Literal manuscript (3.13) instantiated with the genuine full-class
Appell coefficient, rather than a tensor-symmetry premise. -/
theorem actualAppell_tensorSlotSum_square_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    (∑ k : Fin n,
      (KLS.TensorEnergy.tensorSlotSum (thirdCumulantMatrix μ (MomentMap.coordinateVector k)) *ᵥ
        actualAppellCoefficient μ f r) ⬝ᵥ
      (KLS.TensorEnergy.tensorSlotSum (thirdCumulantMatrix μ (MomentMap.coordinateVector k)) *ᵥ
        actualAppellCoefficient μ f r)) ≤
      (∑ k : Fin n, ∑ s : Fin r,
        (KLS.TensorEnergy.tensorSlot s (thirdCumulantMatrix μ (MomentMap.coordinateVector k)) *ᵥ
          actualAppellCoefficient μ f r) ⬝ᵥ
        (KLS.TensorEnergy.tensorSlot s (thirdCumulantMatrix μ (MomentMap.coordinateVector k)) *ᵥ
          actualAppellCoefficient μ f r)) +
      4*(r:ℝ)*((r:ℝ)-1)*(actualAppellCoefficient μ f r ⬝ᵥ actualAppellCoefficient μ f r) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  exact thirdCumulant_tensorSlotSum_square_le hμ (actualAppellCoefficient_symmetric hμ.logConcave hf)

/-- The improved covariance-noise bound for actual Appell coefficients
of every admissible law and every L² test function. -/
theorem actualAppell_noiseCorrection_lower
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (W : Fin n → (Fin r → Fin n) → ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    β*(∑ k : Fin n, W k ⬝ᵥ W k) -
      ((4/(1-β)-2)*(r:ℝ)^2+((4/(1-β)-2)-4)*(r:ℝ))*
        (actualAppellCoefficient μ f r ⬝ᵥ actualAppellCoefficient μ f r) ≤
      ∑ k : Fin n, KLS.TensorEnergy.energyNoiseCorrection (actualAppellCoefficient μ f r)
        (thirdCumulantMatrix μ (MomentMap.coordinateVector k)) (W k) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  exact sum_energyNoiseCorrection_lower_two_slot hμ (actualAppellCoefficient_symmetric hμ.logConcave hf)
    W hβ0 hβ1

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualAppellCoefficient_symmetric
#print axioms KLS.DeterministicBridgeIntegration.actualAppell_tensorSlotSum_square_le
#print axioms KLS.DeterministicBridgeIntegration.actualAppell_noiseCorrection_lower

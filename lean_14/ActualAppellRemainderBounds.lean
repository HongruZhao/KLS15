import ActualAppellLowerContraction

/-! Lower-degree Appell remainder bounds with every labeled subset counted.
The binomial convolution is the manuscript's d_l, without a dimension factor. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric Matrix
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem sum_subsets_card_weight (d : ℕ) (w : ℕ → ℝ) :
    (∑ S : Finset (Fin d), w S.card) =
      ∑ a ∈ Finset.range (d+1), (d.choose a : ℝ)*w a := by
  classical
  rw [← Finset.powerset_univ (α := Fin d),Finset.sum_powerset]
  simp only [Finset.card_univ,Fintype.card_fin,Finset.sum_powersetCard,nsmul_eq_mul]

 def actualLowerConvolution (h : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 2 (d-1), (d.choose a : ℝ)*Real.sqrt (h a*h (d-a+1))

 theorem actualLowerConvolution_eq_subsets (h : ℕ → ℝ) (d : ℕ) :
    actualLowerConvolution h d =
      ∑ S : Finset (Fin d), if 2 ≤ S.card ∧ S.card ≤ d-1 then
        Real.sqrt (h S.card*h (Sᶜ.card+1)) else 0 := by
  classical
  have hc (S : Finset (Fin d)) : Sᶜ.card = d-S.card := by
    have hh : S.card+Sᶜ.card=d := by simp
    omega
  simp_rw [hc]
  have hs := sum_subsets_card_weight d
    (fun a => if 2 ≤ a ∧ a ≤ d-1 then Real.sqrt (h a*h (d-a+1)) else 0)
  apply Eq.trans (b := ∑ a ∈ Finset.range (d+1), (d.choose a : ℝ)*
    (if 2 ≤ a ∧ a ≤ d-1 then Real.sqrt (h a*h (d-a+1)) else 0)) _ hs.symm
  simp_rw [mul_ite,mul_zero]
  rw [← Finset.sum_filter]
  have he : (Finset.range (d+1)).filter (fun a => 2 ≤ a ∧ a ≤ d-1) =
      Finset.Icc 2 (d-1) := by
    ext a
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Icc]
    omega
  rw [he]
  rfl

 def actualAppellProperRemainder (μ : Measure (Space n)) (f : Space n → ℝ)
    (d : ℕ) : (Fin d → Fin n) → ℝ :=
  ∑ S : Finset (Fin d), if 2 ≤ S.card ∧ S.card ≤ d-1 then
    actualSubsetAppellContraction μ f d S else 0

 /-- The norm of every retained subset contraction is bounded by the
 geometric mean of the two already-proved degrees. -/
 theorem actualSubsetAppellContraction_norm_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (hunit : ∫ x, (f x)^2 ∂μ = 1)
    {d : ℕ} (S : Finset (Fin d)) {h : ℕ → ℝ}
    (ha : 0 ≤ h S.card) (hb : 0 ≤ h (Sᶜ.card+1))
    (hA : ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualAppellEnergy μ g S.card ≤ h S.card*(∫ x, (g x)^2 ∂μ))
    (hB : actualAppellEnergy μ f (Sᶜ.card+1) ≤ h (Sᶜ.card+1)*(∫ x, (f x)^2 ∂μ)) :
    ‖(WithLp.toLp 2 (actualSubsetAppellContraction μ f d S) :
        EuclideanSpace ℝ (Fin d → Fin n))‖ ≤ Real.sqrt (h S.card*h (Sᶜ.card+1)) := by
  have hs := actualSubsetAppellContraction_square_le hμ hf S hA
  rw [hunit,mul_one] at hB
  have hs' : (∑ γ : Fin d → Fin n, (actualSubsetAppellContraction μ f d S γ)^2) ≤
      h S.card*h (Sᶜ.card+1) := hs.trans (mul_le_mul_of_nonneg_left hB ha)
  have hnorm : ‖(WithLp.toLp 2 (actualSubsetAppellContraction μ f d S) :
      EuclideanSpace ℝ (Fin d → Fin n))‖^2 =
      ∑ γ : Fin d → Fin n, (actualSubsetAppellContraction μ f d S γ)^2 :=
    EuclideanSpace.real_norm_sq_eq _
  have hp := Real.sq_sqrt (mul_nonneg ha hb)
  have hn := norm_nonneg (WithLp.toLp 2 (actualSubsetAppellContraction μ f d S) :
    EuclideanSpace ℝ (Fin d → Fin n))
  have hr := Real.sqrt_nonneg (h S.card*h (Sᶜ.card+1))
  nlinarith

 /-- Actual (3.8) with its terminal cumulant removed has norm at most d_l.
 Every coefficient-bound premise is a genuine lower-degree norm bound. -/
 theorem actualAppellProperRemainder_norm_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (hunit : ∫ x, (f x)^2 ∂μ = 1)
    {d k : ℕ} (hd : d ≤ k+1) {h : ℕ → ℝ}
    (hh : ∀ r : ℕ, 1 ≤ r → r ≤ k → 0 ≤ h r)
    (hprevious : ∀ r : ℕ, 1 ≤ r → r ≤ k → ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualAppellEnergy μ g r ≤ h r*(∫ x, (g x)^2 ∂μ)) :
    ‖(WithLp.toLp 2 (actualAppellProperRemainder μ f d) :
      EuclideanSpace ℝ (Fin d → Fin n))‖ ≤ actualLowerConvolution h d := by
  classical
  let V := EuclideanSpace ℝ (Fin d → Fin n)
  have he : (WithLp.toLp 2 (actualAppellProperRemainder μ f d) : V) =
      ∑ S : Finset (Fin d), if 2 ≤ S.card ∧ S.card ≤ d-1 then
        (WithLp.toLp 2 (actualSubsetAppellContraction μ f d S) : V) else 0 := by
    apply PiLp.ext
    intro γ
    change (actualAppellProperRemainder μ f d) γ = _
    unfold actualAppellProperRemainder
    simp only [Finset.sum_apply]
    have hp := map_sum (EuclideanSpace.proj γ)
      (fun S : Finset (Fin d) => if 2 ≤ S.card ∧ S.card ≤ d-1 then
        (WithLp.toLp 2 (actualSubsetAppellContraction μ f d S) : V) else 0) Finset.univ
    change _ = ∑ S : Finset (Fin d), _ at hp
    apply Eq.trans _ hp.symm

    apply Finset.sum_congr rfl
    intro S hS
    split_ifs <;> rfl
  rw [he,actualLowerConvolution_eq_subsets]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun S hS => ?_)
  split_ifs with hp
  · have hc : S.card+Sᶜ.card=d := by simp
    have ha1 : 1 ≤ S.card := by omega
    have hak : S.card ≤ k := by omega
    have hb1 : 1 ≤ Sᶜ.card+1 := by omega
    have hbk : Sᶜ.card+1 ≤ k := by omega
    exact actualSubsetAppellContraction_norm_le hμ hf hunit S
      (hh _ ha1 hak) (hh _ hb1 hbk) (hprevious _ ha1 hak) (hprevious _ hb1 hbk f hf)
  · simp

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualLowerConvolution_eq_subsets
#print axioms KLS.DeterministicBridgeIntegration.actualAppellProperRemainder_norm_le

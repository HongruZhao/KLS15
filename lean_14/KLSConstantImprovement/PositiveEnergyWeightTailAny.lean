import KLSConstantImprovement.PositiveEnergyWeightTail

/-! A positive energy weight may have any constant tail from M<=24.
Young parameters are constant from24. This purely finite prefix/tail
normalization permits fair M12/M16/M20 profile comparisons without
changing an analytic generator input. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.PositiveEnergyWeightTailAny
open KLS.DeterministicBridgeNext
open KLSConstantImprovement.PositiveEnergyWeightedDrift
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

abbrev ratioPrefix := PositiveEnergyWeightTail.ratioPrefix

theorem ratio_prefix_tail (young t : ℕ → ℝ) (y z : ℝ) (M : ℕ)
    (hM : M ≤ 24)
    (hy : ∀ d,24 ≤ d → young d=y) (ht : ∀ d,M ≤ d → t d=z)
    (d : ℕ) (hd : 24 ≤ d) :
    ratioPrefix young t d=ratioPrefix young t 24+((d : ℝ)-24)*(y/z) := by
  induction d,hd using Nat.le_induction with
  | base => norm_num
  | succ d hd ih =>
    dsimp only [ratioPrefix] at ih ⊢
    rw [PositiveEnergyWeightTail.ratio_prefix_succ young t d (by omega),ih,
      hy d hd,ht d (by omega)]
    push_cast
    ring

theorem firstCost_tail (young t theta lambda : ℕ → ℝ) (y z : ℝ)
    (hz : z≠0) (M : ℕ) (hM2 : 2 ≤ M) (hM24 : M ≤ 24)
    (hy : ∀ d,24 ≤ d → young d=y) (ht : ∀ d,M ≤ d → t d=z)
    (d : ℕ) (hd : M+22 ≤ d) (hth : theta d=0) (hl : lambda (d-1)=0) :
    firstCost young t theta lambda d=(y/z)*(d : ℝ)+
      (ratioPrefix young t 24+(∑ a ∈ Finset.Icc 2 (M-1),y/t a)-
        ((M : ℝ)+22)*(y/z)) := by
  classical
  rw [PositiveEnergyWeightTail.firstCost_unretained young t theta lambda d (by omega) hth hl]
  have hs : Finset.Icc 2 (d-1)=
      Finset.Icc 2 (d+1-M) ∪ Finset.Icc (d+2-M) (d-1) := by
    ext b
    simp only [Finset.mem_Icc,Finset.mem_union]
    omega
  have hdis : Disjoint (Finset.Icc 2 (d+1-M)) (Finset.Icc (d+2-M) (d-1)) := by
    rw [Finset.disjoint_left]
    intro b hb hc
    simp only [Finset.mem_Icc] at hb hc
    omega
  rw [hs,Finset.sum_union hdis]
  have hlo : (∑ b ∈ Finset.Icc 2 (d+1-M),young b*t d/(t (d-b+1)*t b))=
      ratioPrefix young t (d+2-M) := by
    have hsub : d+2-M-1=d+1-M := by omega
    unfold ratioPrefix PositiveEnergyWeightTail.ratioPrefix
    rw [hsub]
    apply Finset.sum_congr rfl
    intro b hb
    have ha : M ≤ d-b+1 := by simp only [Finset.mem_Icc] at hb;omega
    rw [ht d (by omega),ht (d-b+1) ha]
    field_simp
  have hhi : (∑ b ∈ Finset.Icc (d+2-M) (d-1),young b*t d/(t (d-b+1)*t b))=
      ∑ a ∈ Finset.Icc 2 (M-1),y/t a := by
    apply Finset.sum_bij (fun b _ => d-b+1)
    · intro b hb
      simp only [Finset.mem_Icc] at hb ⊢
      omega
    · intro a ha b hb hab
      simp only [Finset.mem_Icc] at ha hb
      omega
    · intro a ha
      refine ⟨d-a+1,?_,?_⟩
      · simp only [Finset.mem_Icc] at ha ⊢
        omega
      · simp only [Finset.mem_Icc] at ha
        omega
    · intro b hb
      have hb24 : 24 ≤ b := by simp only [Finset.mem_Icc] at hb;omega
      rw [hy b hb24,ht d (by omega),ht b (by omega)]
      field_simp
  rw [hlo,hhi,ratio_prefix_tail young t y z M hM24 hy ht (d+2-M) (by omega)]
  rw [Nat.cast_sub (by omega : M ≤ d+2)]
  push_cast
  ring

end KLSConstantImprovement.PositiveEnergyWeightTailAny
#print axioms KLSConstantImprovement.PositiveEnergyWeightTailAny.firstCost_tail

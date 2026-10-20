import KLSConstantImprovement.PositiveEnergyWeightedBudget

/-! Exact finite-prefix/constant-tail normalization of positive energy weights.
The chosen cutoffs match the current rational profile: t constant from twelve,
Young parameters constant from 24, and the cleared cubic starts at 41. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.PositiveEnergyWeightTail12
open KLS.DeterministicBridgeNext
open KLSConstantImprovement.PositiveEnergyWeightedDrift
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

def ratioPrefix (young t : ℕ → ℝ) (d : ℕ) : ℝ := ∑ b ∈ Finset.Icc 2 (d-1),young b/t b

theorem ratio_prefix_succ (young t : ℕ → ℝ) (d : ℕ) (hd : 2 ≤ d) :
    ratioPrefix young t (d+1)=young d/t d+ratioPrefix young t d := by
  classical
  have hs:Finset.Icc 2 d=insert d (Finset.Icc 2 (d-1)):=by
    ext b;simp only [Finset.mem_Icc,Finset.mem_insert];omega
  have hn:d∉Finset.Icc 2 (d-1):=by simp only [Finset.mem_Icc];omega
  unfold ratioPrefix
  rw [Nat.add_sub_cancel,hs,Finset.sum_insert hn]

theorem ratio_prefix_tail (young t : ℕ → ℝ) (y z : ℝ)
    (hy : ∀ d,24 ≤ d → young d=y) (ht : ∀ d,12 ≤ d → t d=z)
    (d : ℕ) (hd : 24 ≤ d) :
    ratioPrefix young t d=ratioPrefix young t 24+((d : ℝ)-24)*(y/z) := by
  induction d,hd using Nat.le_induction with
  | base=>norm_num
  | succ d hd ih=>
    rw [ratio_prefix_succ young t d (by omega),ih,hy d hd,ht d (by omega)]
    push_cast
    ring

theorem firstCost_unretained (young t theta lambda : ℕ → ℝ) (d : ℕ) (hd : 3 ≤ d)
    (hth : theta d=0) (hl : lambda (d-1)=0) :
    firstCost young t theta lambda d=
      ∑ b ∈ Finset.Icc 2 (d-1),young b*t d/(t (d-b+1)*t b) := by
  classical
  unfold firstCost
  simp only [thetaTriangleCoefficient,selectiveTriangleFraction,hth,hl,sub_zero,ite_self,
    one_pow,mul_one,div_one]
  apply Finset.sum_bij (fun a _=>d-a+1)
  · intro a ha;simp only [Finset.mem_Icc] at ha ⊢;omega
  · intro a ha b hb hab;simp only [Finset.mem_Icc] at ha hb;omega
  · intro b hb
    refine ⟨d-b+1,?_,?_⟩
    · simp only [Finset.mem_Icc] at hb ⊢;omega
    · simp only [Finset.mem_Icc] at hb;omega
  · intro a ha
    have hs:d-(d-a+1)+1=a:=by simp only [Finset.mem_Icc] at ha;omega
    rw [hs]
    ring

theorem firstCost_tail (young t theta lambda : ℕ → ℝ) (y z : ℝ) (hz : z≠0)
    (hy : ∀ d,24 ≤ d → young d=y) (ht : ∀ d,12 ≤ d → t d=z)
    (d : ℕ) (hd : 41 ≤ d) (hth : theta d=0) (hl : lambda (d-1)=0) :
    firstCost young t theta lambda d=(y/z)*(d : ℝ)+
      (ratioPrefix young t 24+(∑ a ∈ Finset.Icc 2 11,y/t a)-34*(y/z)) := by
  classical
  rw [firstCost_unretained young t theta lambda d (by omega) hth hl]
  have hs:Finset.Icc 2 (d-1)=Finset.Icc 2 (d-11) ∪ Finset.Icc (d-10) (d-1):=by
    ext b;simp only [Finset.mem_Icc,Finset.mem_union];omega
  have hdis:Disjoint (Finset.Icc 2 (d-11)) (Finset.Icc (d-10) (d-1)):=by
    rw [Finset.disjoint_left]
    intro b hb hc
    simp only [Finset.mem_Icc] at hb hc
    omega
  rw [hs,Finset.sum_union hdis]
  have hlo:(∑ b ∈ Finset.Icc 2 (d-11),young b*t d/(t (d-b+1)*t b))=
      ratioPrefix young t (d-10) := by
    have hsub:d-10-1=d-11:=by omega
    unfold ratioPrefix
    rw [hsub]
    apply Finset.sum_congr rfl
    intro b hb
    have ha8:12 ≤ d-b+1:=by simp only [Finset.mem_Icc] at hb;omega
    rw [ht d (by omega),ht (d-b+1) ha8]
    field_simp
  have hhi:(∑ b ∈ Finset.Icc (d-10) (d-1),young b*t d/(t (d-b+1)*t b))=
      ∑ a ∈ Finset.Icc 2 11,y/t a := by
    apply Finset.sum_bij (fun b _=>d-b+1)
    · intro b hb;simp only [Finset.mem_Icc] at hb ⊢;omega
    · intro a ha b hb hab;simp only [Finset.mem_Icc] at ha hb;omega
    · intro a ha
      refine ⟨d-a+1,?_,?_⟩
      · simp only [Finset.mem_Icc] at ha ⊢;omega
      · simp only [Finset.mem_Icc] at ha;omega
    · intro b hb
      have hb24:24 ≤ b:=by simp only [Finset.mem_Icc] at hb;omega
      rw [hy b hb24,ht d (by omega),ht b (by omega)]
      field_simp
  rw [hlo,hhi,ratio_prefix_tail young t y z hy ht (d-10) (by omega)]
  rw [Nat.cast_sub (by omega : 10 ≤ d)]
  norm_num
  ring

end KLSConstantImprovement.PositiveEnergyWeightTail12
#print axioms KLSConstantImprovement.PositiveEnergyWeightTail12.firstCost_tail

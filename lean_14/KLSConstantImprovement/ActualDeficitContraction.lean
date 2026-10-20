import KLSConstantImprovement.ActualDeficitHessianExpansion

/-! Finite tensor contractions of the genuine actual-law deficit Hessian. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualDeficitContraction
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open ActualFixedTensorDeficit ActualDeficitHessianExpansion ActualDeficitTensorBounds
open KLSBelow25.CubicSymmetricNoise
variable {n : ℕ}
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

private theorem reorder_five_first {ι : Type*} [Fintype ι] (F : ι→ι→ι→ι→ι→ℝ) :
    (∑ i,∑ j,∑ a,∑ b,∑ c,F i j a b c)=∑ b,∑ i,∑ a,∑ j,∑ c,F i j a b c := by
  calc
    (∑ i,∑ j,∑ a,∑ b,∑ c,F i j a b c) = ∑ i,∑ j,∑ b,∑ a,∑ c,F i j a b c := by
      exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>Finset.sum_comm
    _ = ∑ i,∑ b,∑ j,∑ a,∑ c,F i j a b c := by
      exact Finset.sum_congr rfl fun i _=>Finset.sum_comm
    _ = ∑ b,∑ i,∑ j,∑ a,∑ c,F i j a b c := by
      exact Finset.sum_comm
    _ = ∑ b,∑ i,∑ a,∑ j,∑ c,F i j a b c := by
      exact Finset.sum_congr rfl fun b _=>Finset.sum_congr rfl fun i _=>Finset.sum_comm

private theorem reorder_five_second {ι : Type*} [Fintype ι] (F : ι→ι→ι→ι→ι→ℝ) :
    (∑ i,∑ j,∑ a,∑ b,∑ d,F i j a b d)=∑ a,∑ i,∑ b,∑ j,∑ d,F i j a b d := by
  calc
    (∑ i,∑ j,∑ a,∑ b,∑ d,F i j a b d) = ∑ i,∑ a,∑ j,∑ b,∑ d,F i j a b d := by
      exact Finset.sum_congr rfl fun i _=>Finset.sum_comm
    _ = ∑ a,∑ i,∑ j,∑ b,∑ d,F i j a b d := by
      exact Finset.sum_comm
    _ = ∑ a,∑ i,∑ b,∑ j,∑ d,F i j a b d := by
      exact Finset.sum_congr rfl fun a _=>Finset.sum_congr rfl fun i _=>Finset.sum_comm

private theorem reorder_six_first {ι : Type*} [Fintype ι] (F : ι→ι→ι→ι→ι→ι→ℝ) :
    (∑ i,∑ j,∑ a,∑ b,∑ c,∑ d,F i j a b c d)=∑ a,∑ d,∑ i,∑ b,∑ j,∑ c,F i j a b c d := by
  calc
    (∑ i,∑ j,∑ a,∑ b,∑ c,∑ d,F i j a b c d) = ∑ i,∑ a,∑ j,∑ b,∑ c,∑ d,F i j a b c d := by
      exact Finset.sum_congr rfl fun i _=>Finset.sum_comm
    _ = ∑ a,∑ i,∑ j,∑ b,∑ c,∑ d,F i j a b c d := by
      exact Finset.sum_comm
    _ = ∑ a,∑ i,∑ j,∑ b,∑ d,∑ c,F i j a b c d := by
      exact Finset.sum_congr rfl fun a _=>Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun b _=>Finset.sum_comm
    _ = ∑ a,∑ i,∑ j,∑ d,∑ b,∑ c,F i j a b c d := by
      exact Finset.sum_congr rfl fun a _=>Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>Finset.sum_comm
    _ = ∑ a,∑ i,∑ d,∑ j,∑ b,∑ c,F i j a b c d := by
      exact Finset.sum_congr rfl fun a _=>Finset.sum_congr rfl fun i _=>Finset.sum_comm
    _ = ∑ a,∑ d,∑ i,∑ j,∑ b,∑ c,F i j a b c d := by
      exact Finset.sum_congr rfl fun a _=>Finset.sum_comm
    _ = ∑ a,∑ d,∑ i,∑ b,∑ j,∑ c,F i j a b c d := by
      exact Finset.sum_congr rfl fun a _=>Finset.sum_congr rfl fun d _=>Finset.sum_congr rfl fun i _=>Finset.sum_comm

private theorem reorder_six_second {ι : Type*} [Fintype ι] (F : ι→ι→ι→ι→ι→ι→ℝ) :
    (∑ i,∑ j,∑ a,∑ b,∑ c,∑ d,F i j a b c d)=∑ b,∑ c,∑ i,∑ a,∑ j,∑ d,F i j a b c d := by
  calc
    (∑ i,∑ j,∑ a,∑ b,∑ c,∑ d,F i j a b c d) = ∑ i,∑ j,∑ b,∑ a,∑ c,∑ d,F i j a b c d := by
      exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>Finset.sum_comm
    _ = ∑ i,∑ b,∑ j,∑ a,∑ c,∑ d,F i j a b c d := by
      exact Finset.sum_congr rfl fun i _=>Finset.sum_comm
    _ = ∑ b,∑ i,∑ j,∑ a,∑ c,∑ d,F i j a b c d := by
      exact Finset.sum_comm
    _ = ∑ b,∑ i,∑ j,∑ c,∑ a,∑ d,F i j a b c d := by
      exact Finset.sum_congr rfl fun b _=>Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>Finset.sum_comm
    _ = ∑ b,∑ i,∑ c,∑ j,∑ a,∑ d,F i j a b c d := by
      exact Finset.sum_congr rfl fun b _=>Finset.sum_congr rfl fun i _=>Finset.sum_comm
    _ = ∑ b,∑ c,∑ i,∑ j,∑ a,∑ d,F i j a b c d := by
      exact Finset.sum_congr rfl fun b _=>Finset.sum_comm
    _ = ∑ b,∑ c,∑ i,∑ a,∑ j,∑ d,F i j a b c d := by
      exact Finset.sum_congr rfl fun b _=>Finset.sum_congr rfl fun c _=>Finset.sum_congr rfl fun i _=>Finset.sum_comm

theorem fourthContraction_expanded {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT23 : ∀ i a b,T i a b=T i b a) :
    fourthContraction μ T=∑ i,∑ a,∑ b,∑ c,∑ d,
      T i a b*T i c d*actualFourthCumulantArray μ a b c d := by
  have hs (i : Fin n) : Matrix.IsSymm (T i) := by ext a b;exact hT23 i b a
  unfold fourthContraction
  simp_rw [actualFourthCumulantFlat_eq_tensor_contraction hμ _ (hs _)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro a _
  apply Finset.sum_congr rfl;intro b _
  apply Finset.sum_congr rfl;intro c _
  apply Finset.sum_congr rfl;intro d _
  ring

theorem fourth_swap_middle {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (i j a c : Fin n) :
    actualFourthCumulantArray μ i j a c=actualFourthCumulantArray μ i a j c := by
  have hh:=actualFourthCumulant_first_three_symmetric hμ c (Equiv.swap (1:Fin 3) 2) ![i,j,a]
  simp only [Function.comp_apply,Equiv.swap_apply_def] at hh
  norm_num at hh
  exact hh.symm

def fourthFirst (μ : Measure (Space n)) (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ a,∑ b,∑ c,∑ d,T i a b*T j c d*
    actualFourthCumulantArray μ i j a c*(if b=d then 1 else 0)
def fourthSecond (μ : Measure (Space n)) (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ a,∑ b,∑ c,∑ d,T i a b*T j c d*
    (if a=c then 1 else 0)*actualFourthCumulantArray μ i j b d
def thirdFirst (μ : Measure (Space n)) (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ a,∑ b,∑ c,∑ d,T i a b*T j c d*
    actualThirdCubicArray μ j a c*actualThirdCubicArray μ i b d
def thirdSecond (μ : Measure (Space n)) (T : Array3 (Fin n)) : ℝ :=
  ∑ i,∑ j,∑ a,∑ b,∑ c,∑ d,T i a b*T j c d*
    actualThirdCubicArray μ i a c*actualThirdCubicArray μ j b d

theorem fourthFirst_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) : fourthFirst μ T=fourthContraction μ T := by
  classical
  have he:fourthFirst μ T=∑ i,∑ j,∑ a,∑ b,∑ c,
      T i a b*T j c b*actualFourthCumulantArray μ i j a c := by
    simp [fourthFirst,mul_ite]
  rw [he,reorder_five_first,fourthContraction_expanded hμ T hT23]
  apply Finset.sum_congr rfl;intro b _
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro a _
  apply Finset.sum_congr rfl;intro j _
  apply Finset.sum_congr rfl;intro c _
  rw [hT23 i a b,hT12 i b a,hT23 j c b,hT12 j b c,fourth_swap_middle hμ]

theorem fourthSecond_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) : fourthSecond μ T=fourthContraction μ T := by
  classical
  have he:fourthSecond μ T=∑ i,∑ j,∑ a,∑ b,∑ d,
      T i a b*T j a d*actualFourthCumulantArray μ i j b d := by
    simp [fourthSecond,mul_ite,ite_mul]
  rw [he,reorder_five_second,fourthContraction_expanded hμ T hT23]
  apply Finset.sum_congr rfl;intro a _
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro b _
  apply Finset.sum_congr rfl;intro j _
  apply Finset.sum_congr rfl;intro d _
  rw [hT12 i a b,hT12 j a d,fourth_swap_middle hμ]

theorem thirdFirst_eq (μ : Measure (Space n)) (T : Array3 (Fin n))
    (hT12 : ∀ i j k,T i j k=T j i k) (hT23 : ∀ i j k,T i j k=T i k j) :
    thirdFirst μ T=signedTraceSquare μ T := by
  unfold thirdFirst
  rw [reorder_six_first]
  unfold signedTraceSquare KLSBelow25.CubicCreation.annihilation
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro a _
  apply Finset.sum_congr rfl;intro d _
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro b _
  apply Finset.sum_congr rfl;intro j _
  apply Finset.sum_congr rfl;intro c _
  rw [hT12 i a b,hT23 j c d,hT12 j d c]
  have hm:actualThirdCubicArray μ j a c=actualThirdCubicArray μ j c a :=
    actualThirdCumulant_swap_last μ j a c
  rw [hm]
  ring

theorem thirdSecond_eq (μ : Measure (Space n)) (T : Array3 (Fin n))
    (hT12 : ∀ i j k,T i j k=T j i k) (hT23 : ∀ i j k,T i j k=T i k j) :
    thirdSecond μ T=signedTraceSquare μ T := by
  unfold thirdSecond
  rw [reorder_six_second]
  unfold signedTraceSquare KLSBelow25.CubicCreation.annihilation
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro b _
  apply Finset.sum_congr rfl;intro c _
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro a _
  apply Finset.sum_congr rfl;intro j _
  apply Finset.sum_congr rfl;intro d _
  rw [hT23 i a b,hT12 i b a,hT12 j c d]
  have hm:actualThirdCubicArray μ j b d=actualThirdCubicArray μ j d b :=
    actualThirdCumulant_swap_last μ j b d
  rw [hm]
  ring

theorem contractedDeficitHessian_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (T : Array3 (Fin n)) (hT12 : ∀ i j k,T i j k=T j i k)
    (hT23 : ∀ i j k,T i j k=T i k j) :
    contractedDeficitHessian μ T=12*fourthContraction μ T+
      12*signedTraceSquare μ T-sixthContraction μ T := by
  have he:contractedDeficitHessian μ T=
      6*fourthFirst μ T+6*thirdFirst μ T+6*thirdSecond μ T+6*fourthSecond μ T-
        sixthContraction μ T := by
    rw [contractedDeficitHessian_expansion hμ]
    unfold fourthFirst fourthSecond thirdFirst thirdSecond sixthContraction
    simp only [Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl;intro i _
    apply Finset.sum_congr rfl;intro j _
    apply Finset.sum_congr rfl;intro a _
    apply Finset.sum_congr rfl;intro b _
    apply Finset.sum_congr rfl;intro c _
    apply Finset.sum_congr rfl;intro d _
    unfold hessianEntry
    ring
  rw [he,fourthFirst_eq hμ T hT12 hT23,fourthSecond_eq hμ T hT12 hT23,
    thirdFirst_eq μ T hT12 hT23,thirdSecond_eq μ T hT12 hT23]
  ring

end KLSConstantImprovement.ActualDeficitContraction
#print axioms KLSConstantImprovement.ActualDeficitContraction.fourthContraction_expanded
#print axioms KLSConstantImprovement.ActualDeficitContraction.fourthFirst_eq
#print axioms KLSConstantImprovement.ActualDeficitContraction.fourthSecond_eq
#print axioms KLSConstantImprovement.ActualDeficitContraction.thirdFirst_eq
#print axioms KLSConstantImprovement.ActualDeficitContraction.thirdSecond_eq
#print axioms KLSConstantImprovement.ActualDeficitContraction.contractedDeficitHessian_eq

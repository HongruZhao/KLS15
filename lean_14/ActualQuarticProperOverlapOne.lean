import ActualCubicCreationBound
import ActualFourthCumulantCoordinates

/-! The actual mixed quartic proper creation overlap with one shared slot.
The fourth cumulant is used only as a two-slot symmetric-matrix operator. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLS.TensorEnergy
open KLSBelow25.CubicSymmetricNoise KLSBelow25.CubicCreation
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

private theorem sum_six_reorder {ι : Type*} [Fintype ι]
    (F : ι→ι→ι→ι→ι→ι→ℝ) :
    (∑ i,∑ j,∑ k,∑ l,∑ a,∑ b,F i j k l a b)=
      ∑ a,∑ k,∑ l,∑ i,∑ b,∑ j,F i j k l a b := by
  calc
    (∑ i,∑ j,∑ k,∑ l,∑ a,∑ b,F i j k l a b) = ∑ i,∑ j,∑ k,∑ a,∑ l,∑ b,F i j k l a b := by
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ i,∑ j,∑ a,∑ k,∑ l,∑ b,F i j k l a b := by
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i,∑ a,∑ j,∑ k,∑ l,∑ b,F i j k l a b := by
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a,∑ i,∑ j,∑ k,∑ l,∑ b,F i j k l a b := by
      exact Finset.sum_comm
    _ = ∑ a,∑ i,∑ k,∑ j,∑ l,∑ b,F i j k l a b := by
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a,∑ k,∑ i,∑ j,∑ l,∑ b,F i j k l a b := by
      exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a,∑ k,∑ i,∑ l,∑ j,∑ b,F i j k l a b := by
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a,∑ k,∑ l,∑ i,∑ j,∑ b,F i j k l a b := by
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ a,∑ k,∑ l,∑ i,∑ b,∑ j,F i j k l a b := by
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm

def actualQuarticProperOverlapOne (μ : Measure (Space n)) (f : Space n→ℝ) : ℝ :=
  ∑ i,∑ j,∑ k,∑ l,∑ a,∑ b,
    actualThirdCubicArray μ i j a *
    actualAppellCoefficient μ f 3 (Fin.cons a (Fin.cons k (Fin.cons l Fin.elim0))) *
    actualFourthCumulantArray μ i k l b *
    actualAppellCoefficient μ f 2 (Fin.cons b (Fin.cons j Fin.elim0))

def actualQuarticProperSymmetricSlice (μ : Measure (Space n)) (f : Space n→ℝ)
    (a : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j=>(actualCubicSlotArray μ f a i j+actualCubicSlotArray μ f a j i)/2

 theorem actualQuarticProperSymmetricSlice_isSymm (μ : Measure (Space n))
    (f : Space n→ℝ) (a : Fin n) : (actualQuarticProperSymmetricSlice μ f a).IsSymm := by
  ext i j
  change (actualCubicSlotArray μ f a j i+actualCubicSlotArray μ f a i j)/2=
    (actualCubicSlotArray μ f a i j+actualCubicSlotArray μ f a j i)/2
  ring

 theorem actualQuarticProperSymmetricSlice_square_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n→ℝ} (hf : MemLp f 2 μ) :
    (∑ a,matrixFrobeniusSq (actualQuarticProperSymmetricSlice μ f a))≤
      6*actualAppellEnergy μ f 2 := by
  have he : (∑ a,matrixFrobeniusSq (actualQuarticProperSymmetricSlice μ f a))=
      (1/4:ℝ)*(square (actualCubicSlotArray μ f)+
        square (fun a i j=>actualCubicSlotArray μ f a j i)+
        2*cross (actualCubicSlotArray μ f)) := by
    unfold matrixFrobeniusSq actualQuarticProperSymmetricSlice square cross tripleSum
    simp only [←Finset.sum_add_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hp : square (fun a i j=>actualCubicSlotArray μ f a j i)=
      square (actualCubicSlotArray μ f) := permuted_square (actualCubicSlotArray μ f)
  rw [he,hp]
  have hq := actualCubicSlotArray_square_le_eight hμ f
  have hr := actualCubicSlotArray_cross_le_four hμ hf
  linarith

private theorem fourth_swap_last {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (i j a b : Fin n) :
    actualFourthCumulantArray μ i j a b=actualFourthCumulantArray μ i j b a := by
  rw [actual_fourth_cumulant_coordinate_eq hμ,actual_fourth_cumulant_coordinate_eq hμ]
  have hprod : (fun x : Space n=>x a*x b)=(fun x : Space n=>x b*x a) := by funext x;ring
  rw [hprod]
  ring

private theorem fourth_cycle_first {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (i j a b : Fin n) :
    actualFourthCumulantArray μ i j a b=actualFourthCumulantArray μ j a i b := by
  have h1 := actualFourthCumulant_first_three_symmetric hμ b (Equiv.swap (0:Fin 3) 1) ![i,j,a]
  have h2 := actualFourthCumulant_first_three_symmetric hμ b (Equiv.swap (1:Fin 3) 2) ![j,i,a]
  simp only [Function.comp_apply,Equiv.swap_apply_def] at h1 h2
  norm_num at h1 h2
  exact h1.symm.trans h2.symm

 theorem actualQuarticProperOverlapOne_eq_matrix_pairing {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n→ℝ} (hf : MemLp f 2 μ) :
    actualQuarticProperOverlapOne μ f=
      tripleSum (fun a k l=>actualCubicNextArray μ f a k l*
        actualFourthCumulantFlat μ (actualQuarticProperSymmetricSlice μ f a) k l) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hraw (a i b : Fin n) :
      (∑ j,actualThirdCubicArray μ i j a*actualAppellCoefficient μ f 2 ![b,j])=
        actualCubicSlotArray μ f a i b := by
    unfold actualThirdCubicArray actualCubicSlotArray
    apply Finset.sum_congr rfl
    intro j _
    rw [actualThirdCumulant_cyclic μ i j a,actualAppell_two_swap hμ.logConcave hf b j]
  have hflat (a k l : Fin n) :
      actualFourthCumulantFlat μ (actualQuarticProperSymmetricSlice μ f a) k l=
      ∑ i,∑ b,actualFourthCumulantArray μ i k l b*
        (∑ j,actualThirdCubicArray μ i j a*actualAppellCoefficient μ f 2 ![b,j]) := by
    rw [actualFourthCumulantFlat_eq_tensor_contraction hμ _
      (actualQuarticProperSymmetricSlice_isSymm μ f a)]
    simp_rw [hraw]
    have hs : (∑ i,∑ b,actualFourthCumulantArray μ k l i b*actualCubicSlotArray μ f a b i)=
        ∑ i,∑ b,actualFourthCumulantArray μ k l i b*actualCubicSlotArray μ f a i b := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro b _
      rw [fourth_swap_last hμ k l b i]
    calc
      (∑ i,∑ b,actualFourthCumulantArray μ k l i b *
          actualQuarticProperSymmetricSlice μ f a i b) =
          ((∑ i,∑ b,actualFourthCumulantArray μ k l i b*actualCubicSlotArray μ f a i b)+
           (∑ i,∑ b,actualFourthCumulantArray μ k l i b*actualCubicSlotArray μ f a b i))/2 := by
        simp only [actualQuarticProperSymmetricSlice,mul_div,mul_add]
        simp_rw [←Finset.sum_div,Finset.sum_add_distrib]
      _ = ∑ i,∑ b,actualFourthCumulantArray μ k l i b*actualCubicSlotArray μ f a i b := by
        rw [hs]
        ring
      _ = ∑ i,∑ b,actualFourthCumulantArray μ i k l b*actualCubicSlotArray μ f a i b := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro b _
        rw [(fourth_cycle_first hμ i k l b).symm]
  unfold actualQuarticProperOverlapOne
  rw [sum_six_reorder]
  unfold tripleSum actualCubicNextArray
  simp_rw [hflat,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro j _
  have h3 : Fin.cons a (Fin.cons k (Fin.cons l Fin.elim0))=![a,k,l] := by
    ext z;fin_cases z <;> rfl
  have h2 : Fin.cons b (Fin.cons j Fin.elim0)=![b,j] := by
    ext z;fin_cases z <;> rfl
  rw [h3,h2]
  ring

 theorem actualQuarticProperOverlapOne_sq_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n→ℝ} (hf : MemLp f 2 μ) :
    (actualQuarticProperOverlapOne μ f)^2≤
      216*actualAppellEnergy μ f 3*actualAppellEnergy μ f 2 := by
  let W : Array3 (Fin n) := fun a k l=>
    actualFourthCumulantFlat μ (actualQuarticProperSymmetricSlice μ f a) k l
  have hW : square W≤216*actualAppellEnergy μ f 2 := by
    have hh := Finset.sum_le_sum (fun a (_ : a∈(Finset.univ : Finset (Fin n)))=>
      actual_fourth_cumulant_flat_square_le hμ (actualQuarticProperSymmetricSlice μ f a)
        (actualQuarticProperSymmetricSlice_isSymm μ f a))
    have hs := actualQuarticProperSymmetricSlice_square_le hμ hf
    change square W≤_
    simp only [matrixFrobeniusSq,←Finset.mul_sum] at hh
    change square W≤36*(∑ a,matrixFrobeniusSq (actualQuarticProperSymmetricSlice μ f a)) at hh
    linarith
  rw [actualQuarticProperOverlapOne_eq_matrix_pairing hμ hf]
  have hc := triple_pairing_sq_le (actualCubicNextArray μ f) W
  rw [actualCubicNextArray_square] at hc
  have hb := mul_le_mul_of_nonneg_left hW (actualAppellEnergy_nonneg μ f 3)
  exact hc.trans (by nlinarith)

 theorem actualQuarticProperOverlapOne_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n→ℝ} (hf : MemLp f 2 μ) :
    actualQuarticProperOverlapOne μ f≤
      6*Real.sqrt (6*actualAppellEnergy μ f 3*actualAppellEnergy μ f 2) := by
  have hs := actualQuarticProperOverlapOne_sq_le hμ hf
  have hr := Real.sq_sqrt (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤6)
    (actualAppellEnergy_nonneg μ f 3)) (actualAppellEnergy_nonneg μ f 2))
  have hp := Real.sqrt_nonneg (6*actualAppellEnergy μ f 3*actualAppellEnergy μ f 2)
  nlinarith [sq_nonneg (actualQuarticProperOverlapOne μ f+
    6*Real.sqrt (6*actualAppellEnergy μ f 3*actualAppellEnergy μ f 2))]

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualQuarticProperSymmetricSlice_square_le
#print axioms KLS.DeterministicBridgeIntegration.actualQuarticProperOverlapOne_eq_matrix_pairing
#print axioms KLS.DeterministicBridgeIntegration.actualQuarticProperOverlapOne_sq_le
#print axioms KLS.DeterministicBridgeIntegration.actualQuarticProperOverlapOne_le

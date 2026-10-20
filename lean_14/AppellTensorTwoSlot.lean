import UniversalTwoSlot
import KLS.TensorSlotSumBound
import KLS.ThirdCumulantMatrixSeed

/-! Actual two-slot third-cumulant estimates lifted to symmetric coordinate
arrays. These are the covariance-noise estimates in manuscript (3.13). -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n r : ℕ}

/-- Literal coordinate action in one tensor slot. -/
def coordinateSlot (s : Fin r) (H : Matrix (Fin n) (Fin n) ℝ)
    (T : (Fin r → Fin n) → ℝ) (a : Fin r → Fin n) : ℝ :=
  ∑ j, H (a s) j * T (Function.update a s j)

abbrev ExceptSlot (s : Fin r) := {i : Fin r // i ≠ s}

def insertOne (s : Fin r) (c : ExceptSlot s → Fin n) (j : Fin n)
    (i : Fin r) : Fin n := if h : i=s then j else c ⟨i,h⟩

def splitOne (s : Fin r) : (Fin r → Fin n) ≃ (ExceptSlot s → Fin n) × Fin n where
  toFun x := (fun i => x i, x s)
  invFun p := insertOne s p.1 p.2
  left_inv x := by funext i; simp only [insertOne]; split_ifs <;> simp_all
  right_inv p := by
    rcases p with ⟨c,j⟩
    change (fun i : ExceptSlot s => insertOne s c j i, insertOne s c j s) = (c,j)
    simp only [insertOne, dite_true]
    congr 1
    funext i
    simp only [i.property,dite_false]

 theorem sum_splitOne (s : Fin r) (F : (Fin r → Fin n) → ℝ) :
    (∑ x, F x) = ∑ c : ExceptSlot s → Fin n, ∑ j, F (insertOne s c j) := by
  rw [← (splitOne (n:=n) s).symm.sum_comp F]
  simp only [Fintype.sum_prod_type]
  rfl

 theorem tensorSlot_delta (s : Fin r) (a b : Fin r → Fin n) :
    (∏ i ∈ Finset.univ.erase s, (1 : Matrix (Fin n) (Fin n) ℝ) (a i) (b i)) =
      if (fun i : ExceptSlot s => a i) = (fun i : ExceptSlot s => b i) then 1 else 0 := by
  classical
  by_cases h : (fun i : ExceptSlot s => a i) = (fun i : ExceptSlot s => b i)
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    have his := (Finset.mem_erase.mp hi).1
    have hab : a i=b i := congrFun h ⟨i,his⟩
    change (if a i = b i then (1:ℝ) else 0) = 1
    simp [hab]
  · rw [if_neg h]
    have hh : ∃ i : ExceptSlot s, a i ≠ b i := by
      by_contra hn
      push_neg at hn
      exact h (funext hn)
    obtain ⟨i,hi⟩ := hh
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨i.property,Finset.mem_univ _⟩)
      (by change (if a i = b i then (1:ℝ) else 0) = 0; simp [hi])

/-- The coordinate formula is the exact tensor-slot matrix action already
used by the released cumulant calculus. -/
theorem coordinateSlot_eq_tensorSlot (s : Fin r)
    (H : Matrix (Fin n) (Fin n) ℝ) (T : (Fin r → Fin n) → ℝ) :
    coordinateSlot s H T = KLS.TensorEnergy.tensorSlot s H *ᵥ T := by
  classical
  funext a
  symm
  simp only [Matrix.mulVec,dotProduct,KLS.TensorEnergy.tensorSlot_apply]
  rw [sum_splitOne s]
  have hrestrict (c : ExceptSlot s → Fin n) (j : Fin n) :
      (fun i : ExceptSlot s => insertOne s c j i) = c := by
    funext i
    simp [insertOne,i.property]
  simp_rw [tensorSlot_delta,hrestrict]
  rw [Finset.sum_eq_single (fun i : ExceptSlot s => a i)]
  · apply Finset.sum_congr rfl
    intro j _
    have hins : insertOne s (fun i : ExceptSlot s => a i) j = Function.update a s j := by
      funext i
      by_cases hi : i=s <;> simp [insertOne,Function.update,hi]
    simp [hins,coordinateSlot,insertOne]
  · intro c _ hc
    have hne : (fun i : ExceptSlot s => a i) ≠ c := Ne.symm hc
    simp [hne]
  · simp

/-- The coordinates other than two specified slots. -/
abbrev OtherSlots (s t : Fin r) := {i : Fin r // i ≠ s ∧ i ≠ t}

def insertTwo (s t : Fin r) (c : OtherSlots s t → Fin n)
    (a b : Fin n) (i : Fin r) : Fin n :=
  if hs : i=s then a else if ht : i=t then b else c ⟨i,hs,ht⟩

@[simp] theorem insertTwo_left {s t : Fin r} (hst : s ≠ t)
    (c : OtherSlots s t → Fin n) (a b : Fin n) : insertTwo s t c a b s = a := by
  simp [insertTwo]
@[simp] theorem insertTwo_right {s t : Fin r} (hst : s ≠ t)
    (c : OtherSlots s t → Fin n) (a b : Fin n) : insertTwo s t c a b t = b := by
  simp [insertTwo,hst.symm]
@[simp] theorem insertTwo_other {s t : Fin r}
    (c : OtherSlots s t → Fin n) (a b : Fin n) (i : OtherSlots s t) :
    insertTwo s t c a b i = c i := by
  simp [insertTwo,i.property.1,i.property.2]

def splitTwo {s t : Fin r} (hst : s ≠ t) :
    (Fin r → Fin n) ≃ (OtherSlots s t → Fin n) × Fin n × Fin n where
  toFun x := (fun i => x i, x s, x t)
  invFun p := insertTwo s t p.1 p.2.1 p.2.2
  left_inv x := by
    funext i
    simp only [insertTwo]
    split_ifs with hs ht <;> simp_all
  right_inv p := by
    rcases p with ⟨c,a,b⟩
    simp only [insertTwo_left hst,insertTwo_right hst]
    congr 1
    funext i
    exact insertTwo_other c a b i

 theorem sum_splitTwo {s t : Fin r} (hst : s ≠ t)
    (F : (Fin r → Fin n) → ℝ) :
    (∑ x, F x) = ∑ c : OtherSlots s t → Fin n, ∑ a, ∑ b,
      F (insertTwo s t c a b) := by
  rw [← (splitTwo (n:=n) hst).symm.sum_comp F]
  simp only [Fintype.sum_prod_type]
  rfl

 theorem update_insertTwo_left {s t : Fin r} (hst : s ≠ t)
    (c : OtherSlots s t → Fin n) (a b j : Fin n) :
    Function.update (insertTwo s t c a b) s j = insertTwo s t c j b := by
  funext i
  by_cases his : i=s
  · subst i; simp [insertTwo]
  · simp [Function.update_of_ne his,insertTwo,his]
 theorem update_insertTwo_right {s t : Fin r} (hst : s ≠ t)
    (c : OtherSlots s t → Fin n) (a b j : Fin n) :
    Function.update (insertTwo s t c a b) t j = insertTwo s t c a j := by
  funext i
  by_cases hit : i=t
  · subst i; simp [insertTwo,hst.symm]
  · by_cases his : i=s
    · subst i; simp [insertTwo,hst]
    · simp [Function.update_of_ne hit,insertTwo,his,hit]

 theorem coordinateSlot_insertTwo_left {s t : Fin r} (hst : s ≠ t)
    (H : Matrix (Fin n) (Fin n) ℝ) (T : (Fin r → Fin n) → ℝ)
    (c : OtherSlots s t → Fin n) (a b : Fin n) :
    coordinateSlot s H T (insertTwo s t c a b) =
      (H * (show Matrix (Fin n) (Fin n) ℝ from fun i j => T (insertTwo s t c i j))) a b := by
  simp only [coordinateSlot,insertTwo_left hst,update_insertTwo_left hst,Matrix.mul_apply]
 theorem coordinateSlot_insertTwo_right {s t : Fin r} (hst : s ≠ t)
    (H : Matrix (Fin n) (Fin n) ℝ) (T : (Fin r → Fin n) → ℝ)
    (c : OtherSlots s t → Fin n) (a b : Fin n) :
    coordinateSlot t H T (insertTwo s t c a b) =
      ((show Matrix (Fin n) (Fin n) ℝ from fun i j => T (insertTwo s t c i j)) * H.transpose) a b := by
  simp only [coordinateSlot,insertTwo_right hst,update_insertTwo_right hst,
    Matrix.mul_apply,Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

 theorem sum_matrix_products_eq_trace (A B : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, A i j * B i j) = (A.transpose * B).trace := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.transpose_apply]
  exact Finset.sum_comm

 theorem matrix_two_slot_pairing (U H : Matrix (Fin n) (Fin n) ℝ)
    (hU : U.IsSymm) (hH : H.IsSymm) :
    (∑ a, ∑ b, (H*U) a b * (U*H.transpose) a b) = (U*H*U*H).trace := by
  rw [sum_matrix_products_eq_trace,Matrix.transpose_mul,hU.eq,hH.eq]
  simp only [Matrix.mul_assoc]

/-- Full tensor symmetry in coordinates. -/
def CoordinateTensorSymmetric (T : (Fin r → Fin n) → ℝ) : Prop :=
  ∀ (s t : Fin r) (a : Fin r → Fin n), T (a ∘ Equiv.swap s t) = T a

 theorem insertTwo_swap {s t : Fin r} (hst : s ≠ t)
    (c : OtherSlots s t → Fin n) (a b : Fin n) :
    insertTwo s t c a b ∘ Equiv.swap s t = insertTwo s t c b a := by
  funext i
  by_cases his : i=s
  · subst i; simp [hst,Function.comp_def]
  · by_cases hit : i=t
    · subst i; simp [hst,Function.comp_def]
    · simp [Function.comp_def,Equiv.swap_apply_of_ne_of_ne his hit,insertTwo,his,hit]

 theorem slice_isSymm {T : (Fin r → Fin n) → ℝ}
    (hT : CoordinateTensorSymmetric T) {s t : Fin r} (hst : s ≠ t)
    (c : OtherSlots s t → Fin n) : (show Matrix (Fin n) (Fin n) ℝ from fun a b => T (insertTwo s t c a b)).IsSymm := by
  apply Matrix.IsSymm.ext
  intro a b
  simpa only [insertTwo_swap hst c a b] using hT s t (insertTwo s t c a b)

/-- Distinct covariance-noise slots have the improved constant four. -/
theorem thirdCumulant_distinct_slot_pairing_le_four
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {T : (Fin r → Fin n) → ℝ} (hT : CoordinateTensorSymmetric T)
    {s t : Fin r} (hst : s ≠ t) :
    (∑ k : Fin n, ∑ a : Fin r → Fin n,
      coordinateSlot s (thirdCumulantMatrix μ (MomentMap.coordinateVector k)) T a *
      coordinateSlot t (thirdCumulantMatrix μ (MomentMap.coordinateVector k)) T a)
      ≤ 4 * ∑ a, T a ^ 2 := by
  let H := fun k => thirdCumulantMatrix μ (MomentMap.coordinateVector k)
  have hH k : (H k).IsSymm := thirdCumulantMatrix_isSymm _ _
  change (∑ k, ∑ a, coordinateSlot s (H k) T a * coordinateSlot t (H k) T a) ≤ _
  simp_rw [sum_splitTwo hst,coordinateSlot_insertTwo_left hst,
    coordinateSlot_insertTwo_right hst]
  rw [Finset.sum_comm]
  have hslice (c : OtherSlots s t → Fin n) :=
    thirdCumulant_two_slot_four_universal hμ (fun a b => T (insertTwo s t c a b))
      (slice_isSymm hT hst c)
  simp_rw [matrix_two_slot_pairing _ _ (slice_isSymm hT hst _) (hH _)]
  have hb := Finset.sum_le_sum (s:=Finset.univ) (fun c _ => hslice c)
  simpa only [matrixFrobeniusSq,← Finset.mul_sum] using hb

 theorem slotSum_square_le_of_distinct_pairing
    {ι : Type*} [Fintype ι] {q : ℕ} (V : Fin q → Fin r → ι → ℝ) (C : ℝ)
    (hcross : ∀ s t : Fin r, s ≠ t →
      (∑ k : Fin q, V k s ⬝ᵥ V k t) ≤ C) :
    (∑ k : Fin q, (∑ s, V k s) ⬝ᵥ (∑ s, V k s)) ≤
      (∑ k : Fin q, ∑ s : Fin r, V k s ⬝ᵥ V k s) + C*(r:ℝ)*((r:ℝ)-1) := by
  classical
  have hrow (s : Fin r) :
      (∑ t : Fin r, ∑ k : Fin q, V k s ⬝ᵥ V k t) ≤
        (∑ k : Fin q, V k s ⬝ᵥ V k s) + C*((r:ℝ)-1) := by
    have hr : 1 ≤ r := by have := s.isLt; omega
    have hb := Finset.sum_le_sum (s:=Finset.univ.erase s)
      (fun t ht => hcross s t (Ne.symm (Finset.mem_erase.mp ht).1))
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ s)]
    have hcard : ((Finset.univ.erase s).card : ℝ) = (r:ℝ)-1 := by
      simp [Finset.card_erase_of_mem, Nat.cast_sub hr]
    simpa only [Finset.sum_const, nsmul_eq_mul, hcard, mul_comm C, add_comm] using
      add_le_add_right hb (∑ k : Fin q, V k s ⬝ᵥ V k s)
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun s _ => hrow s)
  have hid : (∑ k : Fin q, (∑ s, V k s) ⬝ᵥ (∑ s, V k s)) =
      ∑ s : Fin r, ∑ t : Fin r, ∑ k : Fin q, V k s ⬝ᵥ V k t := by
    simp only [sum_dotProduct,dotProduct_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro k _
    exact dotProduct_comm _ _
  rw [hid]
  convert hsum using 1
  rw [Finset.sum_add_distrib,Finset.sum_comm]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

/-- Manuscript (3.13), with the actual third-cumulant slices and the
released tensor-slot matrix operators. -/
theorem thirdCumulant_tensorSlotSum_square_le
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {T : (Fin r → Fin n) → ℝ} (hT : CoordinateTensorSymmetric T) :
    (∑ k : Fin n,
      (KLS.TensorEnergy.tensorSlotSum (thirdCumulantMatrix μ (MomentMap.coordinateVector k)) *ᵥ T) ⬝ᵥ
      (KLS.TensorEnergy.tensorSlotSum (thirdCumulantMatrix μ (MomentMap.coordinateVector k)) *ᵥ T)) ≤
      (∑ k : Fin n, ∑ s : Fin r,
        (KLS.TensorEnergy.tensorSlot s (thirdCumulantMatrix μ (MomentMap.coordinateVector k)) *ᵥ T) ⬝ᵥ
        (KLS.TensorEnergy.tensorSlot s (thirdCumulantMatrix μ (MomentMap.coordinateVector k)) *ᵥ T)) +
      4*(r:ℝ)*((r:ℝ)-1)*(T ⬝ᵥ T) := by
  let H := fun k => thirdCumulantMatrix μ (MomentMap.coordinateVector k)
  have hc (s t : Fin r) (hst : s ≠ t) :=
    thirdCumulant_distinct_slot_pairing_le_four hμ hT hst
  simp only [coordinateSlot_eq_tensorSlot,← pow_two] at hc
  have hb := slotSum_square_le_of_distinct_pairing
    (fun k s => KLS.TensorEnergy.tensorSlot s (H k) *ᵥ T) (4*(T ⬝ᵥ T))
    (fun s t hst => by simpa only [dotProduct,H,pow_two] using hc s t hst)
  simpa only [KLS.TensorEnergy.tensorSlotSum,Matrix.sum_mulVec] using
    (show (∑ k : Fin n,
      (∑ s : Fin r, KLS.TensorEnergy.tensorSlot s (H k) *ᵥ T) ⬝ᵥ
      (∑ s : Fin r, KLS.TensorEnergy.tensorSlot s (H k) *ᵥ T)) ≤ _ from
      hb.trans_eq (by ring))

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.thirdCumulant_distinct_slot_pairing_le_four

#print axioms KLS.DeterministicBridgeIntegration.thirdCumulant_tensorSlotSum_square_le

import PairTensorDisjointAlgebra
import PairTensorCoordinateSlots
import PairTensorDisjointFrame

/-! Lossless transfer of a same-test cubic mixed estimate to every higher
ordered symmetric rank. The cubic estimate is an explicit hypothesis;
this module supplies only its algebraic rank-slicing bridge. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.MixedCubicRankSlicing
open KLSBelow25.PairTensor
variable {ι : Type*} [Fintype ι] {r : ℕ}
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

def cubicSlice (H : Tensor (ι := ι) (r+3)) (z : Fin r → ι) :
    ι → ι → ι → ℝ := fun i j k => H (Fin.cons i (Fin.cons j (Fin.cons k z)))

def cubicInsertion (κ C : ι → ι → ι → ℝ) :
    KLSBelow25.QuarticSymmetricNoise.Array4 ι :=
  fun i j k l => ∑ m, κ i j m * C m k l

def cubicEnergy (C : ι → ι → ι → ℝ) : ℝ := ∑ i, ∑ j, ∑ k, C i j k ^ 2

def cubicR (κ C : ι → ι → ι → ℝ) : ℝ :=
  KLSBelow25.QuarticSymmetricNoise.cross (cubicInsertion κ C)

def cubicS (κ C : ι → ι → ι → ℝ) : ℝ :=
  KLSBelow25.QuarticSymmetricNoise.disjoint (cubicInsertion κ C)

def rankR (κ : ι → ι → ι → ℝ) (H : Tensor (ι := ι) (r+3)) : ℝ :=
  pairing (kernel κ H (incidentPair (0 : Fin (r+3))))
    (kernel κ H (incidentPair (1 : Fin (r+3))))

def rankS (κ : ι → ι → ι → ℝ) (H : Tensor (ι := ι) (r+3)) : ℝ :=
  pairing (kernel κ H (incidentPair (0 : Fin (r+3))))
    (kernel κ H (disjointPair r))

omit [Fintype ι] in
theorem cubicSlice_swap12 (H : Tensor (ι := ι) (r+3)) (hH : Symmetric H)
    (z : Fin r → ι) (i j k : ι) : cubicSlice H z i j k = cubicSlice H z j i k := by
  have hh := hH (Equiv.swap (0 : Fin (r+3)) 1)
    (Fin.cons i (Fin.cons j (Fin.cons k z)))
  rw [cons_two_exchangeSwap] at hh
  exact hh.symm

omit [Fintype ι] in
theorem cubicSlice_swap23 (H : Tensor (ι := ι) (r+3)) (hH : Symmetric H)
    (z : Fin r → ι) (i j k : ι) : cubicSlice H z i j k = cubicSlice H z i k j := by
  have hh := symmetric_cons_tail H hH (Equiv.swap (0 : Fin (r+2)) 1) i
    (Fin.cons j (Fin.cons k z))
  rw [cons_two_exchangeSwap] at hh
  exact hh.symm

theorem sum_first_three (F : Tensor (ι := ι) (r+3)) :
    (∑ a, F a) = ∑ i, ∑ j, ∑ k, ∑ z,
      F (Fin.cons i (Fin.cons j (Fin.cons k z))) := by
  rw [sum_cons_coordinates]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_cons_coordinates]
  apply Finset.sum_congr rfl
  intro j _
  rw [sum_cons_coordinates]

theorem sum_three_tail (F : ι → ι → ι → (Fin r → ι) → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ z, F i j k z) = ∑ z, ∑ i, ∑ j, ∑ k, F i j k z := by
  calc
    _ = ∑ i, ∑ j, ∑ z, ∑ k, F i j k z :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i, ∑ z, ∑ j, ∑ k, F i j k z :=
      Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem square_eq_sum_cubicEnergy (H : Tensor (ι := ι) (r+3)) :
    square H = ∑ z : Fin r → ι, cubicEnergy (cubicSlice H z) := by
  unfold square cubicEnergy cubicSlice
  rw [sum_first_three, sum_three_tail]

theorem sum_four_tail (F : ι → ι → ι → ι → (Fin r → ι) → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, ∑ z, F i j k l z) =
      ∑ z, ∑ i, ∑ j, ∑ k, ∑ l, F i j k l z := by
  calc
    _ = ∑ i, ∑ j, ∑ k, ∑ z, ∑ l, F i j k l z :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ z, ∑ k, ∑ l, F i j k l z :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i, ∑ z, ∑ j, ∑ k, ∑ l, F i j k l z :=
      Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

omit [Fintype ι] in
private theorem update_first (j k l m : ι) (z : Fin r → ι) :
    Function.update (show Fin (r+3) → ι from Fin.cons j (Fin.cons k (Fin.cons l z)))
      (0 : Fin (r+3)) m =
      Fin.cons m (Fin.cons k (Fin.cons l z)) := Fin.update_cons_zero _ _ _

omit [Fintype ι] in
private theorem update_second (j k l m : ι) (z : Fin r → ι) :
    Function.update (show Fin (r+3) → ι from Fin.cons j (Fin.cons k (Fin.cons l z)))
      (1 : Fin (r+3)) m =
      Fin.cons j (Fin.cons m (Fin.cons l z)) := by
  rw [← Fin.succ_zero_eq_one, ← Fin.cons_update, Fin.update_cons_zero]

theorem rankR_eq_sum_cubicR (κ : ι → ι → ι → ℝ)
    (hκ : ∀ i j m, κ i j m = κ j i m)
    (H : Tensor (ι := ι) (r+3)) (hH : Symmetric H) :
    rankR κ H = ∑ z : Fin r → ι, cubicR κ (cubicSlice H z) := by
  unfold rankR pairing
  rw [sum_first_four_coordinates]
  simp_rw [kernel_incidentPair_cons κ hκ H hH]
  simp only [Fin.cons_zero, Fin.cons_one, update_first, update_second]
  rw [sum_four_tail]
  unfold cubicR KLSBelow25.QuarticSymmetricNoise.cross
    KLSBelow25.QuarticSymmetricNoise.quadSum cubicInsertion cubicSlice
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [show H (Fin.cons j (Fin.cons x (Fin.cons l z))) =
      H (Fin.cons x (Fin.cons j (Fin.cons l z))) from cubicSlice_swap12 H hH z j x l]

theorem rankS_eq_sum_cubicS (κ : ι → ι → ι → ℝ)
    (hκ : ∀ i j m, κ i j m = κ j i m)
    (H : Tensor (ι := ι) (r+3)) (hH : Symmetric H) :
    rankS κ H = ∑ z : Fin r → ι, cubicS κ (cubicSlice H z) := by
  unfold rankS
  rw [kernel_disjoint_pairing_eq κ hκ H hH]
  have hv : kernelInFrame κ H (consFrame (r+2)) = disjointInsertion κ H := rfl
  rw [hv, swapPairs_eq_disjointSwap]
  unfold pairing
  rw [sum_first_four_coordinates]
  simp only [cons_four_disjointSwap, disjointInsertion, Fin.cons_zero,
    Fin.cons_one, Fin.tail_cons]
  rw [sum_four_tail]
  rfl

/-- The two adjacent swaps express full symmetry of a cubic array. The
same cubic is used for both terms; independent matrix slices are never
substituted for it. -/
def CubicMixedBound (κ : ι → ι → ι → ℝ) (β B : ℝ) : Prop :=
  ∀ C : ι → ι → ι → ℝ,
    (∀ i j k, C i j k = C j i k) →
    (∀ i j k, C i j k = C i k j) →
    cubicR κ C + β * cubicS κ C ≤ B * cubicEnergy C

/-- A universal cubic mixed estimate transfers unchanged to every ordered
symmetric rank d>=3. No positivity assumption on either mixed term is
needed, and no combinatorial or dimension factor is lost. -/
theorem rank_mixed_le_of_cubic (κ : ι → ι → ι → ℝ)
    (hκ : ∀ i j m, κ i j m = κ j i m)
    (H : Tensor (ι := ι) (r+3)) (hH : Symmetric H)
    {β B : ℝ} (hMixed : CubicMixedBound κ β B) :
    rankR κ H + β * rankS κ H ≤ B * square H := by
  rw [rankR_eq_sum_cubicR κ hκ H hH, rankS_eq_sum_cubicS κ hκ H hH,
    square_eq_sum_cubicEnergy, Finset.mul_sum, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun z _ =>
    hMixed (cubicSlice H z) (cubicSlice_swap12 H hH z) (cubicSlice_swap23 H hH z)

/-- Convert the same-test curve at beta=B/A into the precise weighted
mixed loss appearing in the conditional optimizer. -/
theorem mixed_weighted_absorption {A B R S E c : ℝ} (hA : 0 < A)
    (hMix : R + (B/A)*S ≤ (4+4*(B/A)+c*(B/A)^2)*E) :
    A*R+B*S ≤ (4*A+4*B+c*B^2/A)*E := by
  have hh := mul_le_mul_of_nonneg_left hMix hA.le
  have hl : A*(R+(B/A)*S) = A*R+B*S := by field_simp
  have hr : A*((4+4*(B/A)+c*(B/A)^2)*E) =
      (4*A+4*B+c*B^2/A)*E := by field_simp
  rw [hl,hr] at hh
  exact hh

/-- The nonnegative-Q branch retains the Gram residual before applying
the mixed bound. The effective coefficients have no additional factor. -/
theorem mixed_low_branch {aW q Q A0 B0 R S d L E N : ℝ}
    (hraw : aW+q*Q-A0*R-B0*S ≤ N) (hq : 0 ≤ q)
    (hres : (d-2)*S ≤ Q+(d-3)*R)
    (hMixed : (A0+(d-3)*q)*R+(B0-(d-2)*q)*S ≤ L*E) :
    aW-L*E ≤ N := by
  have hh := mul_le_mul_of_nonneg_left hres hq
  nlinarith

/-- In the nonpositive-Q branch the existing diagonal estimate supplies
exactly the extra loss -8q; the R/S budget is still on one common test. -/
theorem mixed_high_branch {aW q Q A0 B0 R S L E N : ℝ}
    (hraw : aW+q*Q-A0*R-B0*S ≤ N) (hq : q ≤ 0)
    (hQ : Q ≤ 8*E) (hMixed : A0*R+B0*S ≤ L*E) :
    aW-(-8*q+L)*E ≤ N := by
  have hh := mul_le_mul_of_nonpos_left hQ hq
  nlinarith

end KLSConstantImprovement.MixedCubicRankSlicing
#print axioms KLSConstantImprovement.MixedCubicRankSlicing.cubicSlice_swap12
#print axioms KLSConstantImprovement.MixedCubicRankSlicing.cubicSlice_swap23
#print axioms KLSConstantImprovement.MixedCubicRankSlicing.square_eq_sum_cubicEnergy
#print axioms KLSConstantImprovement.MixedCubicRankSlicing.rankR_eq_sum_cubicR
#print axioms KLSConstantImprovement.MixedCubicRankSlicing.rankS_eq_sum_cubicS
#print axioms KLSConstantImprovement.MixedCubicRankSlicing.rank_mixed_le_of_cubic
#print axioms KLSConstantImprovement.MixedCubicRankSlicing.mixed_weighted_absorption
#print axioms KLSConstantImprovement.MixedCubicRankSlicing.mixed_low_branch
#print axioms KLSConstantImprovement.MixedCubicRankSlicing.mixed_high_branch

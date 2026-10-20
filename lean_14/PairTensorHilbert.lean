import PairTensorKernel

/-! The literal ordered tensor coordinates are embedded in their actual
finite real Hilbert space, with exactly the ordered Hilbert--Schmidt norm. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.PairTensor
variable {ι : Type*} [Fintype ι] {d r : ℕ}

abbrev HilbertTensor (d : ℕ) := EuclideanSpace ℝ (Fin d→ι)
def toHilbert (T : Tensor (ι := ι) d) : HilbertTensor (ι := ι) d := WithLp.toLp 2 T
omit [Fintype ι] in
@[simp] theorem toHilbert_apply (T : Tensor (ι := ι) d) (a : Fin d→ι) : toHilbert T a=T a := rfl

theorem toHilbert_inner (S T : Tensor (ι := ι) d) :
    inner ℝ (toHilbert S) (toHilbert T)=pairing S T := by
  simpa only [toHilbert,pairing,star_trivial,dotProduct,mul_comm] using
    EuclideanSpace.inner_toLp_toLp S T

theorem toHilbert_norm_sq (T : Tensor (ι := ι) d) : ‖toHilbert T‖^2=square T := by
  rw [←real_inner_self_eq_norm_sq,toHilbert_inner]
  simp only [pairing,square,pow_two]

omit [Fintype ι] in
@[simp] theorem toHilbert_add (S T : Tensor (ι := ι) d) :
    toHilbert (S+T)=toHilbert S+toHilbert T := rfl
omit [Fintype ι] in
@[simp] theorem toHilbert_smul (c : ℝ) (T : Tensor (ι := ι) d) :
    toHilbert (c • T)=c • toHilbert T := rfl

omit [Fintype ι] in
theorem toHilbert_sum {α : Type*} (s : Finset α) (T : α→Tensor (ι := ι) d) :
    toHilbert (∑ a∈s,T a)=∑ a∈s,toHilbert (T a) := by
  ext a
  simp only [WithLp.ofLp_sum,Finset.sum_apply,toHilbert_apply]

theorem pair_sum_toHilbert (κ : ι→ι→ι→ℝ) (T : Tensor (ι := ι) (r+1)) :
    PairProjection.sumPairs (fun e => toHilbert (kernel κ T e))=toHilbert (creation κ T) := by
  ext a
  simp only [PairProjection.sumPairs,WithLp.ofLp_sum,Finset.sum_apply,toHilbert_apply,creation]

end KLSBelow25.PairTensor
#print axioms KLSBelow25.PairTensor.toHilbert_inner
#print axioms KLSBelow25.PairTensor.toHilbert_norm_sq
#print axioms KLSBelow25.PairTensor.pair_sum_toHilbert

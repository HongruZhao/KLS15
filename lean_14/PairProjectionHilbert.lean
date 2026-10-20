import PairProjectionCounts

/-! Exact Hilbert identities for an unordered-pair family. Actual tensor
sources discharge the finite Gram premise by coordinate permutation. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace KLSBelow25.PairProjection
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem gram_linear (U : Pair N → H) {Q R S : ℝ} (h : Gram U Q R S)
    (e f : Pair N) :
    inner ℝ (U e) (U f) = (if e=f then Q-2*R+S else 0)+
      (R-S)*((e.val∩f.val).card : ℝ)+S := by
  rw [h e f]
  by_cases hef : e=f
  · subst f
    simp only [ite_true,Finset.inter_self,e.property,Nat.cast_ofNat]
    ring
  · by_cases hn : (e.val∩f.val).Nonempty
    · simp only [hef,ite_false,hn,ite_true,pair_intersection_card_of_ne hef hn,
        Nat.cast_one,zero_add,mul_one]
      ring
    · have hz : (e.val∩f.val).card=0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hn)
      simp [hef,hn,hz]

def row (N : ℕ) (Q R S : ℝ) : ℝ :=
  Q+2*((N : ℝ)-2)*R+(((N : ℝ)-2)*((N : ℝ)-3)/2)*S

theorem gram_row_sum (U : Pair N → H) {Q R S : ℝ} (h : Gram U Q R S)
    (e : Pair N) : (∑ f,inner ℝ (U e) (U f))=row N Q R S := by
  simp_rw [gram_linear U h e]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.mul_sum,
    sum_pair_intersection]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [card_pair_real]
  unfold row
  ring

theorem sumPairs_sq (U : Pair N → H) {Q R S : ℝ} (h : Gram U Q R S) :
    ‖sumPairs U‖^2=((N : ℝ)*((N : ℝ)-1)/2)*row N Q R S := by
  rw [←real_inner_self_eq_norm_sq]
  unfold sumPairs
  simp_rw [sum_inner,inner_sum,gram_row_sum U h]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_pair_real]

theorem star_sq (U : Pair N → H) {Q R S : ℝ} (h : Gram U Q R S)
    (i : Fin N) :
    ‖star U i‖^2=((N : ℝ)-1)*Q+((N : ℝ)-1)*((N : ℝ)-2)*R := by
  classical
  let A := Finset.univ.filter (fun e : Pair N => i∈e.val)
  have hg (e : Pair N) (he : e∈A) (f : Pair N) (hf : f∈A) :
      inner ℝ (U e) (U f)=(if e=f then Q-R else 0)+R := by
    rw [h e f]
    by_cases hef : e=f
    · simp [hef]
    · have hn : (e.val∩f.val).Nonempty :=
        ⟨i,Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp he).2,(Finset.mem_filter.mp hf).2⟩⟩
      simp [hef,hn]
  have hs (e : Pair N) (he : e∈A) :
      (∑ f∈A,inner ℝ (U e) (U f))=Q-R+(A.card : ℝ)*R := by
    calc
      _=∑ f∈A,((if e=f then Q-R else 0)+R) :=
        Finset.sum_congr rfl fun f hf => hg e he f hf
      _=_ := by
        rw [Finset.sum_add_distrib]
        simp [he]
  rw [←real_inner_self_eq_norm_sq]
  change inner ℝ (∑ e∈A,U e) (∑ e∈A,U e)=_
  simp_rw [sum_inner,inner_sum]
  have hh : (∑ e∈A,∑ f∈A,inner ℝ (U e) (U f))=
      (A.card : ℝ)*(Q-R+(A.card : ℝ)*R) := by
    rw [Finset.sum_congr rfl hs]
    simp only [Finset.sum_const,nsmul_eq_mul]
  rw [hh]
  have hc : (A.card : ℝ)=(N : ℝ)-1 := pair_incidence_count i
  rw [hc]
  ring

theorem projection_sq (U : Pair N → H) {Q R S : ℝ} (h : Gram U Q R S)
    (hN : 0<N) :
    ‖projection U‖^2=(2*((N : ℝ)-1)/(N : ℝ))*row N Q R S := by
  have hn : (N : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hN)
  rw [projection,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,sumPairs_sq U h]
  field_simp

theorem star_projection_inner (U : Pair N → H) {Q R S : ℝ}
    (h : Gram U Q R S) (i : Fin N) :
    inner ℝ (star U i) (projection U)=‖projection U‖^2 := by
  have hN : 0<N := by have hi:=i.isLt; omega
  rw [projection_sq U h hN]
  rw [projection,inner_smul_right]
  unfold star sumPairs
  simp_rw [sum_inner,inner_sum,gram_row_sum U h]
  simp only [Finset.sum_const,nsmul_eq_mul]
  rw [pair_incidence_count]
  ring

theorem residual_sq (U : Pair N → H) {Q R S : ℝ}
    (h : Gram U Q R S) (i : Fin N) :
    ‖star U i-projection U‖^2=
      (((N : ℝ)-1)*((N : ℝ)-2)/(N : ℝ))*
        (Q+((N : ℝ)-4)*R-((N : ℝ)-3)*S) := by
  have hN : 0<N := by have hi:=i.isLt; omega
  have hn : (N : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hN)
  rw [norm_sub_sq_real,star_projection_inner U h i,star_sq U h i,
    projection_sq U h hN]
  unfold row
  field_simp
  ring

theorem residual_relation (U : Pair N → H) {Q R S : ℝ}
    (h : Gram U Q R S) (hN : 3≤N) :
    ((N : ℝ)-3)*S≤Q+((N : ℝ)-4)*R := by
  let i : Fin N := ⟨0,by omega⟩
  have hh : 0≤‖star U i-projection U‖^2 := sq_nonneg _
  rw [residual_sq U h i] at hh
  have hp : 0<((N : ℝ)-1)*((N : ℝ)-2)/(N : ℝ) := by
    have hr : (3 : ℝ)≤N := by exact_mod_cast hN
    exact div_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hb := (mul_nonneg_iff_of_pos_left hp).mp hh
  linarith

theorem constant_pairing (U : Pair N → H) (W : H) {t : ℝ}
    (h : ∀ e,inner ℝ W (U e)=t) (i : Fin N) :
    inner ℝ W (star U i)=inner ℝ W (projection U) := by
  have hN : 0<N := by have hi:=i.isLt; omega
  have hn : (N : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hN)
  unfold star projection sumPairs
  simp_rw [inner_smul_right,inner_sum,h]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [pair_incidence_count,card_pair_real]
  field_simp

end KLSBelow25.PairProjection
#print axioms KLSBelow25.PairProjection.sumPairs_sq
#print axioms KLSBelow25.PairProjection.star_sq
#print axioms KLSBelow25.PairProjection.projection_sq
#print axioms KLSBelow25.PairProjection.star_projection_inner
#print axioms KLSBelow25.PairProjection.residual_sq
#print axioms KLSBelow25.PairProjection.residual_relation
#print axioms KLSBelow25.PairProjection.constant_pairing

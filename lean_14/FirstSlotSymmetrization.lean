import PairTensorKernel

/-! Full symmetrization of a tensor symmetric in every position except
possibly its first. Exact norm and exchange formulas use ordered coordinates. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.PairTensor
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {r : ℕ} {ι : Type*} [Fintype ι]

def TailSymmetric (M : Tensor (ι:=ι) (r+2)) : Prop :=
  ∀ (π : Equiv.Perm (Fin (r+2))), π 0=0 → ∀ a,M (a∘π)=M a

def firstSym (M : Tensor (ι:=ι) (r+2)) : Tensor (ι:=ι) (r+2) :=
  fun a => (1/(r+2 : ℕ)) * ∑ s : Fin (r+2),M (a∘Equiv.swap 0 s)

def exchange (M : Tensor (ι:=ι) (r+2)) : ℝ :=
  pairing M (fun a => M (a∘Equiv.swap 0 1))

theorem sum_comp_perm {d : ℕ} (F : Tensor (ι:=ι) d) (π : Equiv.Perm (Fin d)) :
    (∑ a,F (a∘π))=∑ a,F a := by
  exact Fintype.sum_equiv (Equiv.arrowCongr π.symm (Equiv.refl ι)) _ _
    (fun a => by congr 1)

theorem pairing_comp_perm {d : ℕ} (M T : Tensor (ι:=ι) d)
    (π : Equiv.Perm (Fin d)) :
    pairing (fun a => M (a∘π)) (fun a => T (a∘π))=pairing M T := by
  exact sum_comp_perm (fun a => M a*T a) π

theorem pairing_comm {d : ℕ} (M T : Tensor (ι:=ι) d) : pairing M T=pairing T M := by
  unfold pairing
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

omit [Fintype ι] in theorem firstSym_symmetric (M : Tensor (ι:=ι) (r+2)) (hM : TailSymmetric M) :
    Symmetric (firstSym M) := by
  intro π a
  have ht (s : Fin (r+2)) : M ((a∘π)∘Equiv.swap 0 s)=M (a∘Equiv.swap 0 (π s)) := by
    let θ := (Equiv.swap (0 : Fin (r+2)) s).trans π
    let η := θ.trans (Equiv.swap (0 : Fin (r+2)) (π s))
    have hη : η 0=0 := by simp [η,θ,Equiv.trans_apply]
    have hh := hM η hη (a∘Equiv.swap 0 (π s))
    have he : (a∘Equiv.swap 0 (π s))∘η=(a∘π)∘Equiv.swap 0 s := by
      ext j
      simp [Function.comp_def,η,θ]
    rwa [he] at hh
  unfold firstSym
  congr 1
  simp_rw [ht]
  exact Fintype.sum_equiv π _ _ (fun _ => rfl)

theorem pairing_firstSym (P M : Tensor (ι:=ι) (r+2)) (hP : Symmetric P) :
    pairing P (firstSym M)=pairing P M := by
  have hs (s : Fin (r+2)) :
      (∑ a,P a*M (a∘Equiv.swap 0 s))=pairing P M := by
    calc
      _=∑ a,P (a∘Equiv.swap 0 s)*M (a∘Equiv.swap 0 s) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [hP (Equiv.swap 0 s) a]
      _=pairing P M := pairing_comp_perm P M (Equiv.swap 0 s)
  unfold pairing firstSym
  simp_rw [mul_left_comm (P _) (1/(r+2 : ℕ)),Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [←Finset.mul_sum,hs]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hz : (r+2 : ℝ)≠0 := by positivity
  norm_num only [Nat.cast_add,Nat.cast_ofNat]
  unfold pairing
  field_simp

theorem pairing_swap_first (M : Tensor (ι:=ι) (r+2)) (hM : TailSymmetric M)
    (s : Fin (r+2)) (hs : s≠0) :
    pairing M (fun a => M (a∘Equiv.swap 0 s))=exchange M := by
  let π := Equiv.swap (1 : Fin (r+2)) s
  have hπ0 : π 0=0 := by
    exact Equiv.swap_apply_of_ne_of_ne (by norm_num) (Ne.symm hs)
  have hπs : π s=1 := Equiv.swap_apply_right _ _
  have he (a : Fin (r+2)→ι) :
      (a∘π)∘Equiv.swap 0 s=(a∘Equiv.swap 0 1)∘π := by
    ext j
    change a (π (Equiv.swap 0 s j))=a (Equiv.swap 0 1 (π j))
    rw [←π.injective.swap_apply,hπ0,hπs]
  calc
    _=pairing (fun a => M (a∘π)) (fun a => M ((a∘π)∘Equiv.swap 0 s)) :=
      (pairing_comp_perm M (fun a => M (a∘Equiv.swap 0 s)) π).symm
    _=exchange M := by
      unfold pairing exchange
      unfold pairing
      simp_rw [he,hM π hπ0]

theorem firstSym_square (M : Tensor (ι:=ι) (r+2)) (hM : TailSymmetric M) :
    square (firstSym M)=(square M+(r+1 : ℕ)*exchange M)/(r+2 : ℕ) := by
  have hp : square (firstSym M)=pairing M (firstSym M) := by
    calc
      _=pairing (firstSym M) (firstSym M) := by simp only [square,pairing,pow_two]
      _=pairing (firstSym M) M := pairing_firstSym _ _ (firstSym_symmetric M hM)
      _=pairing M (firstSym M) := pairing_comm _ _
  have hs (s : Fin (r+2)) :
      (∑ a,M a*M (a∘Equiv.swap 0 s))=
        (if s=0 then square M-exchange M else 0)+exchange M := by
    by_cases hz : s=0
    · subst s
      simp [square,exchange,pow_two]
    · rw [show (∑ a,M a*M (a∘Equiv.swap 0 s))=exchange M from pairing_swap_first M hM s hz]
      simp [hz]
  rw [hp]
  unfold pairing firstSym
  simp_rw [mul_left_comm (M _) (1/(r+2 : ℕ)),Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [←Finset.mul_sum,hs]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  ring

theorem exchange_le_square (M : Tensor (ι:=ι) (r+2)) : exchange M ≤ square M := by
  have hh := square_nonneg (fun a => M a-M (a∘Equiv.swap (0 : Fin (r+2)) 1))
  have he : square (fun a => M a-M (a∘Equiv.swap (0 : Fin (r+2)) 1))=
      square M-2*exchange M+square M := by
    calc
      _=square M-2*exchange M+square (fun a => M (a∘Equiv.swap 0 1)) := by
        unfold square exchange pairing
        rw [Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _=_ := by
        unfold square
        rw [sum_comp_perm (fun a => M a^2) (Equiv.swap (0 : Fin (r+2)) 1)]
  rw [he] at hh
  linarith

theorem exchange_le_firstSym_square (M : Tensor (ι:=ι) (r+2))
    (hM : TailSymmetric M) : exchange M ≤ square (firstSym M) := by
  rw [firstSym_square M hM]
  have hn : (0 : ℝ)<(r+2 : ℕ) := by positivity
  apply (le_div_iff₀ hn).mpr
  have hh := exchange_le_square M
  norm_num only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  nlinarith

end KLSBelow25.PairTensor
#print axioms KLSBelow25.PairTensor.firstSym_symmetric
#print axioms KLSBelow25.PairTensor.pairing_firstSym
#print axioms KLSBelow25.PairTensor.firstSym_square
#print axioms KLSBelow25.PairTensor.exchange_le_firstSym_square

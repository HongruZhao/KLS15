import ActualTripleOverlapOneBound
import TripleTensorRepresentatives

noncomputable section
open scoped BigOperators
namespace KLSBelow25.TripleTensor
open PairTensor
variable {r : ℕ}
set_option maxHeartbeats 1200000
set_option maxRecDepth 5000

theorem overlapOneSwap_eq_overlapOnePerm (r : ℕ) : overlapOneSwap r=overlapOnePerm r := by
  apply Equiv.ext
  intro a
  refine Fin.cases ?_ (fun b=>?_) a
  · simp [overlapOneSwap,overlapOnePerm,Equiv.swap_apply_def,Fin.ext_iff,
      Fin.coe_ofNat_eq_mod,Nat.mod_eq_of_lt (by omega : 2<r+5),Nat.mod_eq_of_lt (by omega : 3<r+5),
      Nat.mod_eq_of_lt (by omega : 4<r+5)]
  · rw [overlapOneSwap,fixHeadPerm_succ]
    refine Fin.cases ?_ (fun c=>?_) b
    · change (disjointSwap r 0).succ=overlapOnePerm r 1
      rw [disjointSwap_zero]
      simp [overlapOnePerm,Equiv.swap_apply_def,Fin.ext_iff,Fin.coe_ofNat_eq_mod,
        Nat.mod_eq_of_lt (by omega : 2<r+4),Nat.mod_eq_of_lt (by omega : 2<r+5),
        Nat.mod_eq_of_lt (by omega : 3<r+5),Nat.mod_eq_of_lt (by omega : 4<r+5)]
    · refine Fin.cases ?_ (fun d=>?_) c
      · change (disjointSwap r 1).succ=overlapOnePerm r 2
        rw [disjointSwap_one]
        simp [overlapOnePerm,Equiv.swap_apply_def,Fin.ext_iff,Fin.coe_ofNat_eq_mod,
          Nat.mod_eq_of_lt (by omega : 1<r+5),Nat.mod_eq_of_lt (by omega : 2<r+5),
          Nat.mod_eq_of_lt (by omega : 3<r+4),
          Nat.mod_eq_of_lt (by omega : 3<r+5),Nat.mod_eq_of_lt (by omega : 4<r+5)]
      · refine Fin.cases ?_ (fun e=>?_) d
        · change (disjointSwap r 2).succ=overlapOnePerm r 3
          rw [disjointSwap_two]
          simp [overlapOnePerm,Equiv.swap_apply_def,Fin.ext_iff,Fin.coe_ofNat_eq_mod,
            Nat.mod_eq_of_lt (by omega : 1<r+5),Nat.mod_eq_of_lt (by omega : 2<r+5),
            Nat.mod_eq_of_lt (by omega : 4<r+5)]
        · refine Fin.cases ?_ (fun f=>?_) e
          · change (disjointSwap r 3).succ=overlapOnePerm r 4
            rw [disjointSwap_three]
            simp [overlapOnePerm,Equiv.swap_apply_def,Fin.ext_iff,Fin.coe_ofNat_eq_mod,
              Nat.mod_eq_of_lt (by omega : 4<r+5),Nat.mod_eq_of_lt (by omega : 1<r+5),
              Nat.mod_eq_of_lt (by omega : 3<r+5)]
          · have h0 : f.succ.succ.succ.succ≠(0 : Fin (r+4)) := by
              simp [Fin.ext_iff,Fin.coe_ofNat_eq_mod]
            have h1 : f.succ.succ.succ.succ≠(1 : Fin (r+4)) := by
              simp [Fin.ext_iff,Fin.coe_ofNat_eq_mod]
            have h2 : f.succ.succ.succ.succ≠(2 : Fin (r+4)) := by
              simp [Fin.ext_iff,Fin.coe_ofNat_eq_mod,Nat.mod_eq_of_lt (by omega : 2<r+4)]
            have h3 : f.succ.succ.succ.succ≠(3 : Fin (r+4)) := by
              simp [Fin.ext_iff,Fin.coe_ofNat_eq_mod,Nat.mod_eq_of_lt (by omega : 3<r+4)]
            have h1' : f.succ.succ.succ.succ.succ≠(1 : Fin (r+5)) := by
              simp [Fin.ext_iff,Fin.coe_ofNat_eq_mod]
            have h2' : f.succ.succ.succ.succ.succ≠(2 : Fin (r+5)) := by
              simp [Fin.ext_iff,Fin.coe_ofNat_eq_mod,Nat.mod_eq_of_lt (by omega : 2<r+5)]
            have h3' : f.succ.succ.succ.succ.succ≠(3 : Fin (r+5)) := by
              simp [Fin.ext_iff,Fin.coe_ofNat_eq_mod,Nat.mod_eq_of_lt (by omega : 3<r+5)]
            have h4' : f.succ.succ.succ.succ.succ≠(4 : Fin (r+5)) := by
              simp [Fin.ext_iff,Fin.coe_ofNat_eq_mod,Nat.mod_eq_of_lt (by omega : 4<r+5)]
            simp [overlapOnePerm,disjointSwap,Equiv.swap_apply_def,h0,h1,h2,h3,h1',h2',h3',h4']

end KLSBelow25.TripleTensor
namespace KLS.DeterministicBridgeIntegration
open KLS KLSBelow25.PairTensor KLSBelow25.TripleTensor MeasureTheory
variable {n r : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem actual_triple_overlap_one_representative_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (H : Tensor (ι:=Fin n) (r+3)) (hH : Symmetric H) :
    pairing (kernel (actualFourthCumulantArray μ) H (prefixTriple (r+2)))
      (kernel (actualFourthCumulantArray μ) H (overlapOneTriple r)) ≤ 36*square H := by
  have hh := actual_triple_overlap_one_le hμ H hH
  rw [overlapOneSwap_eq_overlapOnePerm] at hh
  have he : kernel (actualFourthCumulantArray μ) H (overlapOneTriple r)=
      fun a=>kernel (actualFourthCumulantArray μ) H (prefixTriple (r+2)) (a∘overlapOnePerm r) := by
    funext a
    exact (kernel_comp _ (actualFourthCumulant_first_three_symmetric hμ) H hH
      (overlapOnePerm r) (prefixTriple (r+2)) a).symm
  rw [he,kernel_prefix_eq_cons _ (actualFourthCumulant_first_three_symmetric hμ) H hH]
  exact hh

end KLS.DeterministicBridgeIntegration
#print axioms KLSBelow25.TripleTensor.overlapOneSwap_eq_overlapOnePerm
#print axioms KLS.DeterministicBridgeIntegration.actual_triple_overlap_one_representative_le

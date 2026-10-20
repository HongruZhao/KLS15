import PairTensorRepresentatives

/-! The disjoint pair representative is the literal exchange of the first
and second coordinate pairs. No norm estimate is used in this identification. -/
noncomputable section
open scoped BigOperators
namespace KLSBelow25.PairTensor
variable {r : ℕ} {ι : Type*} [Fintype ι]

theorem kernel_incident_zero_eq_cons (κ : ι → ι → ι → ℝ)
    (hκ : ∀ i j m,κ i j m=κ j i m) (H : Tensor (ι := ι) (r+1))
    (hH : Symmetric H) :
    kernel κ H (incidentPair (0 : Fin (r+1))) = kernelInFrame κ H (consFrame r) := by
  funext a
  apply kernelInFrame_eq κ hκ H hH (incidentPair 0)
  · exact pairFrame_inl_mem _
  · exact pairFrame_inr_not_mem _
  · intro i
    fin_cases i <;> simp [incidentPair]
  · intro i
    simp only [consFrame_right,incidentPair,Finset.mem_insert,Finset.mem_singleton,not_or,Fin.succ_ne_zero,not_false_eq_true,true_and]
    intro h
    exact Fin.succ_ne_zero i (Fin.succ_inj.mp h)

theorem kernel_disjoint_eq (κ : ι → ι → ι → ℝ)
    (hκ : ∀ i j m,κ i j m=κ j i m) (H : Tensor (ι := ι) (r+3))
    (hH : Symmetric H) :
    kernel κ H (disjointPair r) =
      fun a => kernelInFrame κ H (consFrame (r+2)) (a ∘ swapPairs r) := by
  funext a
  rw [disjointPair,←kernel_comp κ hκ H hH]
  rw [kernel_incident_zero_eq_cons κ hκ H hH]

theorem kernel_disjoint_pairing_eq (κ : ι → ι → ι → ℝ)
    (hκ : ∀ i j m,κ i j m=κ j i m) (H : Tensor (ι := ι) (r+3))
    (hH : Symmetric H) :
    pairing (kernel κ H (incidentPair (0 : Fin (r+3)))) (kernel κ H (disjointPair r)) =
      pairing (kernelInFrame κ H (consFrame (r+2)))
        (fun a => kernelInFrame κ H (consFrame (r+2)) (a ∘ swapPairs r)) := by
  rw [kernel_disjoint_eq κ hκ H hH,kernel_incident_zero_eq_cons κ hκ H hH]

end KLSBelow25.PairTensor
#print axioms KLSBelow25.PairTensor.kernel_disjoint_pairing_eq

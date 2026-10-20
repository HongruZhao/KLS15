import TensorHodgeAdjointDefect

/-! Exact finite ordered-coordinate exterior two-form kinetic identity.
The 1/3 factor is the physical normalized three-form norm. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {ι : Type*} [Fintype ι]

lemma finite_triple_sum_swap12 (f : ι → ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ i, ∑ j, ∑ k, f j i k := Finset.sum_comm

lemma finite_triple_sum_swap23 (f : ι → ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ i, ∑ j, ∑ k, f i k j :=
  Finset.sum_congr rfl (fun i _ => Finset.sum_comm)

lemma finite_triple_sum_cycle (f : ι → ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ i, ∑ j, ∑ k, f k i j := by
  rw [finite_triple_sum_swap12]
  exact finite_triple_sum_swap23 (fun i j k => f j i k)

/-- The literal exterior derivative energy is gradient energy minus twice
the mixed derivative energy, for a coefficient tensor skew in its last
two slots. No geometric estimate is assumed. -/
theorem exteriorTwoForm_kinetic_identity (T : ι → ι → ι → ℝ)
    (hs : ∀ i j k, T i j k = -T i k j) :
    (1 / 3 : ℝ) * (∑ i, ∑ j, ∑ k, (T i j k - T j i k + T k i j) ^ 2) =
      (∑ i, ∑ j, ∑ k, (T i j k) ^ 2) -
        2 * ∑ i, ∑ j, ∑ k, T i j k * T j i k := by
  have hB : (∑ i, ∑ j, ∑ k, (T j i k) ^ 2) =
      ∑ i, ∑ j, ∑ k, (T i j k) ^ 2 :=
    (finite_triple_sum_swap12 (fun i j k => (T i j k) ^ 2)).symm
  have hC : (∑ i, ∑ j, ∑ k, (T k i j) ^ 2) =
      ∑ i, ∑ j, ∑ k, (T i j k) ^ 2 :=
    (finite_triple_sum_cycle (fun i j k => (T i j k) ^ 2)).symm
  have hAC : (∑ i, ∑ j, ∑ k, T i j k * T k i j) =
      -(∑ i, ∑ j, ∑ k, T i j k * T j i k) := by
    rw [finite_triple_sum_swap23]
    have he : (∑ i, ∑ j, ∑ k, T i k j * T j i k) =
        ∑ i, ∑ j, ∑ k, -(T i j k * T j i k) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [hs i k j]
      ring
    rw [he]
    simp only [Finset.sum_neg_distrib]
  have hBC : (∑ i, ∑ j, ∑ k, T j i k * T k i j) =
      ∑ i, ∑ j, ∑ k, T i j k * T j i k := by
    rw [finite_triple_sum_swap12]
    have he : (∑ i, ∑ j, ∑ k, T i j k * T k j i) =
        -(∑ i, ∑ j, ∑ k, T i j k * T k i j) := by
      have hterm : (∑ i, ∑ j, ∑ k, T i j k * T k j i) =
          ∑ i, ∑ j, ∑ k, -(T i j k * T k i j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        rw [hs k j i]
        ring
      rw [hterm]
      simp only [Finset.sum_neg_distrib]
    rw [he, hAC, neg_neg]
  have hex (i j k : ι) : (T i j k - T j i k + T k i j) ^ 2 =
      (T i j k) ^ 2 + (T j i k) ^ 2 + (T k i j) ^ 2 -
        2 * (T i j k * T j i k) + 2 * (T i j k * T k i j) -
        2 * (T j i k * T k i j) := by ring
  simp_rw [hex]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hB, hC, hAC, hBC]
  ring

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.exteriorTwoForm_kinetic_identity

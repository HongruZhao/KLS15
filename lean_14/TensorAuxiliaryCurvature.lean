import TensorCreationRow
import SymmetricTupleContraction

/-! The physical auxiliary curvature operator in ordered symmetric
coordinates. Every auxiliary slot contributes the same quadratic form;
the equality is proved by literal slot insertion, not by assuming a
normalized multiplicity basis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n r : ℕ}

/-- The literal second quantization of a real coordinate matrix, with
one contribution for each auxiliary tensor slot. -/
def tensorAuxiliaryCurvatureForm (K : Fin n → Fin n → ℝ)
    (f : OrderedTensorIndex n (r + 1) → ℝ) : ℝ :=
  ∑ a, ∑ k : Fin (r + 1), ∑ j : Fin n,
    K (a k) j * f a * f (Function.update a k j)

lemma tensorAuxiliaryCurvatureForm_slot
    (K : Fin n → Fin n → ℝ) (f : OrderedTensorIndex n (r + 1) → ℝ)
    (hs : ∀ a b, List.Perm (List.ofFn a) (List.ofFn b) → f a = f b)
    (k : Fin (r + 1)) :
    (∑ a, ∑ j : Fin n, K (a k) j * f a * f (Function.update a k j)) =
      ∑ I : OrderedTensorIndex n r, ∑ i, ∑ j,
        K i j * f (Fin.cons i I) * f (Fin.cons j I) := by
  calc
    _ = ∑ p : Fin n × OrderedTensorIndex n r, ∑ j : Fin n,
        K ((Fin.insertNth (α := fun _ => Fin n) k p.1 p.2) k) j *
          f (Fin.insertNth (α := fun _ => Fin n) k p.1 p.2) *
          f (Function.update (Fin.insertNth (α := fun _ => Fin n) k p.1 p.2) k j) := by
      symm
      exact Fintype.sum_equiv (Fin.insertNthEquiv (fun _ : Fin (r + 1) => Fin n) k)
        _ _ (fun _ => rfl)
    _ = ∑ p : Fin n × OrderedTensorIndex n r, ∑ j : Fin n,
        K p.1 j * f (Fin.cons p.1 p.2) * f (Fin.cons j p.2) := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro j _
      rw [Fin.insertNth_apply_same, Fin.update_insertNth]
      rw [hs _ _ (KLSBelow25.ofFn_insertNth_perm_cons k p.1 p.2),
        hs _ _ (KLSBelow25.ofFn_insertNth_perm_cons k j p.2)]
    _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- The actual all-slot curvature form equals the physical rank times
its first-slot form on symmetric tensors. -/
theorem tensorAuxiliaryCurvatureForm_eq_rank_mul
    (K : Fin n → Fin n → ℝ) (f : OrderedTensorIndex n (r + 1) → ℝ)
    (hs : ∀ a b, List.Perm (List.ofFn a) (List.ofFn b) → f a = f b) :
    tensorAuxiliaryCurvatureForm K f =
      (r + 1 : ℕ) * ∑ I : OrderedTensorIndex n r, ∑ i, ∑ j,
        K i j * f (Fin.cons i I) * f (Fin.cons j I) := by
  unfold tensorAuxiliaryCurvatureForm
  rw [Finset.sum_comm]
  simp_rw [tensorAuxiliaryCurvatureForm_slot K f hs]
  simp

/-- The real Hessian lower bound is inherited by the literal auxiliary
curvature, with the exact auxiliary rank. -/
theorem tensorAuxiliaryCurvatureForm_lower
    (K : Fin n → Fin n → ℝ) (f : OrderedTensorIndex n (r + 1) → ℝ)
    (hs : ∀ a b, List.Perm (List.ofFn a) (List.ofFn b) → f a = f b)
    {a : ℝ} (hlower : ∀ v : Fin n → ℝ,
      a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (K *ᵥ v)) :
    (r + 1 : ℕ) * a * (∑ I, (f I) ^ 2) ≤ tensorAuxiliaryCurvatureForm K f := by
  rw [tensorAuxiliaryCurvatureForm_eq_rank_mul K f hs]
  have h (I : OrderedTensorIndex n r) :
      a * (∑ i, (f (Fin.cons i I)) ^ 2) ≤
        ∑ i, ∑ j, K i j * f (Fin.cons i I) * f (Fin.cons j I) := by
    have hv := hlower (fun i => f (Fin.cons i I))
    simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, pow_two,
      mul_assoc, mul_left_comm, mul_comm] using hv
  have hsum := Finset.sum_le_sum (fun I (_ : I ∈ Finset.univ) => h I)
  rw [← Finset.mul_sum] at hsum
  have he : (∑ I : OrderedTensorIndex n r, ∑ i : Fin n,
      (f (Fin.cons i I)) ^ 2) = ∑ I, (f I) ^ 2 := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ p : Fin n × OrderedTensorIndex n r, (f (Fin.cons p.1 p.2)) ^ 2 :=
        (Fintype.sum_prod_type _).symm
      _ = _ := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (r + 1) => Fin n))
        _ _ (fun _ => rfl)
  rw [he] at hsum
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsum
    (Nat.cast_nonneg (r + 1) : (0 : ℝ) ≤ (r + 1 : ℕ))

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorAuxiliaryCurvatureForm_eq_rank_mul
#print axioms KLS.DeterministicBridgeIntegration.tensorAuxiliaryCurvatureForm_lower

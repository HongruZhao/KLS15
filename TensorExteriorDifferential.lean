import TensorZeroAuxiliaryFiber

/-! Literal normalized exterior differentials on the actual fully
symmetric one-form fibers. The b constraint is proved from full symmetry. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n q : ℕ}

def tensorExteriorOneDerivativeMatrix (n q : ℕ) :
    TensorTwoFormIndex n q → Fin n → TensorOneFormIndex n q → ℝ := fun z k a =>
  (1 / Real.sqrt 2) *
    ((if z.1 = a.1 ∧ k = z.2.1 ∧ a.2 = z.2.2 then 1 else 0) -
      (if z.1 = a.1 ∧ k = z.2.2 ∧ a.2 = z.2.1 then 1 else 0))

def tensorExteriorOneDifferential (f : TensorOneFormIndex n q → Space n → ℝ)
    (z : TensorTwoFormIndex n q) (x : Space n) : ℝ :=
  (1 / Real.sqrt 2) * (coordinateDerivative (f (z.1, z.2.2)) z.2.1 x -
    coordinateDerivative (f (z.1, z.2.1)) z.2.2 x)

lemma tensorExteriorOne_matrixDifferential
    (f : TensorOneFormIndex n q → Space n → ℝ) (z : TensorTwoFormIndex n q) (x : Space n) :
    matrixDifferential (tensorExteriorOneDerivativeMatrix n q) f z x =
      tensorExteriorOneDifferential f z x := by
  rcases z with ⟨I, i, j⟩
  classical
  simp [matrixDifferential, tensorExteriorOneDerivativeMatrix, tensorExteriorOneDifferential,
    mul_sub, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, Fintype.sum_prod_type,
    Finset.sum_ite_irrel, and_comm]
  simp [ite_and]

lemma fullSymmetricOneForm_auxiliary
    {f : TensorOneFormIndex n q → Space n → ℝ}
    (hf : ∀ x, (WithLp.toLp 2 (fun a => f a x)) ∈ tensorOneFormSymmetricFiber n q)
    (I J : OrderedTensorIndex n q) (hp : List.Perm (List.ofFn I) (List.ofFn J)) (i : Fin n) :
    f (I, i) = f (J, i) := by
  funext x
  apply (mem_tensorOneFormSymmetricFiber_iff _).mp (hf x) (I, i) (J, i)
  simpa only [List.ofFn_cons] using hp.cons i

lemma fullSymmetricOneForm_cons_swap
    {f : TensorOneFormIndex n (q + 1) → Space n → ℝ}
    (hf : ∀ x, (WithLp.toLp 2 (fun a => f a x)) ∈ tensorOneFormSymmetricFiber n (q + 1))
    (I : OrderedTensorIndex n q) (i j : Fin n) :
    f (Fin.cons i I, j) = f (Fin.cons j I, i) := by
  funext x
  apply (mem_tensorOneFormSymmetricFiber_iff _).mp (hf x) (Fin.cons i I, j) (Fin.cons j I, i)
  simpa only [List.ofFn_cons] using List.Perm.swap i j (List.ofFn I)

/-- The actual d₁ maps the fully symmetric one-form fiber into the literal
auxiliary-symmetric skew bω=0 two-form fiber. -/
theorem tensorExteriorOneDifferential_compatible
    {f : TensorOneFormIndex n q → Space n → ℝ}
    (hf : ∀ x, (WithLp.toLp 2 (fun a => f a x)) ∈ tensorOneFormSymmetricFiber n q)
    (x : Space n) : TensorTwoFormCompatible (fun z => tensorExteriorOneDifferential f z x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro I J hp i j
    dsimp only [tensorExteriorOneDifferential]
    rw [fullSymmetricOneForm_auxiliary hf I J hp i, fullSymmetricOneForm_auxiliary hf I J hp j]
  · intro I i j
    dsimp only [tensorExteriorOneDifferential]
    ring
  · intro I i j k
    cases q with
    | zero => simp only [Nat.cast_zero, Real.sqrt_zero, zero_mul]
    | succ q =>
      have hI : I = Fin.cons (I 0) (Fin.tail I) := (Fin.cons_self_tail I).symm
      rw [hI]
      simp only [tensorAuxReplaceFirst_cons, tensorExteriorOneDifferential]
      rw [fullSymmetricOneForm_cons_swap hf (Fin.tail I) i k,
        fullSymmetricOneForm_cons_swap hf (Fin.tail I) i j,
        fullSymmetricOneForm_cons_swap hf (Fin.tail I) j k]
      ring

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorExteriorOneDifferential_compatible

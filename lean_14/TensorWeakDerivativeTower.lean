import IteratedTensorPrimitives
import KLS.WeightedCompactL2Maps
import KLS.DirectionalWordLeibniz

/-! Literal local weak derivatives of the constructed all-rank primitive
tower, including its compact localization product rule. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace
namespace KLS.DeterministicBridgeIntegration
variable {n s : ℕ} {φ : Space n → ℝ}

def tensorWordLp (U : (k : ℕ) → OrderedTensorField φ k) (L : List (Fin n)) :
    Lp ℝ 2 (potentialMeasure φ) := U L.length L.get

lemma tensorWordLp_cons (U : (k : ℕ) → OrderedTensorField φ k)
    (L : List (Fin n)) (i : Fin n) :
    tensorWordLp U (i :: L) = U (L.length + 1) (Fin.cons i L.get) := by
  change U (L.length + 1) (i :: L).get = U (L.length + 1) (Fin.cons i L.get)
  have he : (i :: L).get = Fin.cons i L.get := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> simp
  exact congrArg (fun I => U (L.length + 1) I) he

lemma tensorWordLp_memLp_restrict (hφ : Continuous φ)
    (U : (k : ℕ) → OrderedTensorField φ k) (L : List (Fin n))
    {K : Set (Space n)} (hK : IsCompact K) :
    MemLp (tensorWordLp U L) 2 (volume.restrict K) :=
  KLS.MemLp.restrict_volume_of_potentialMeasure (Lp.memLp _) hφ hK

lemma tensorWordLp_weak_identity (hφ : ContDiff ℝ 1 φ)
    (U : (k : ℕ) → OrderedTensorField φ k)
    (hgraph : ∀ k, k < s → ∃ V : TensorPrimitive (φ := φ) (OrderedTensorIndex n k),
      finitePrimitiveValue (OrderedTensorIndex n k) V = U k ∧
        ∀ I i, weightedH1Derivative φ i (V I) = U (k + 1) (Fin.cons i I))
    (L : List (Fin n)) (hL : L.length < s) (i : Fin n)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∫ x, tensorWordLp U L x * coordinateDerivative ψ i x) =
      -(∫ x, tensorWordLp U (i :: L) x * ψ x) := by
  obtain ⟨V, hv, hd⟩ := hgraph L.length hL
  have hv' : weightedH1Value φ (V L.get) = tensorWordLp U L :=
    congrArg (fun T : OrderedTensorField φ L.length => T L.get) hv
  have he := weightedH1_unweighted_weak_identity hφ (V L.get) hψ hc i
  rw [hv', hd, ← tensorWordLp_cons U L i] at he
  exact he

lemma tensorWordLp_compact_product (hφ : ContDiff ℝ 1 φ)
    (U : (k : ℕ) → OrderedTensorField φ k)
    (hgraph : ∀ k, k < s → ∃ V : TensorPrimitive (φ := φ) (OrderedTensorIndex n k),
      finitePrimitiveValue (OrderedTensorIndex n k) V = U k ∧
        ∀ I i, weightedH1Derivative φ i (V I) = U (k + 1) (Fin.cons i I))
    (L : List (Fin n)) (hL : L.length < s) (i : Fin n)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) :
    MemLp (fun x => χ x * tensorWordLp U L x) 2 volume ∧
    ∃ g : Lp ℝ 2 (volume : Measure (Space n)),
      ((g : Space n → ℝ) =ᵐ[volume] fun x =>
        χ x * tensorWordLp U (i :: L) x + coordinateDerivative χ i x * tensorWordLp U L x) ∧
      HasWeakCoordinateDerivative (fun x => χ x * tensorWordLp U L x) i g := by
  obtain ⟨V, hv, hd⟩ := hgraph L.length hL
  have hv' : weightedH1Value φ (V L.get) = tensorWordLp U L :=
    congrArg (fun T : OrderedTensorField φ L.length => T L.get) hv
  have he := weightedH1_compact_mul_hasWeakCoordinateDerivative hφ (V L.get) hχ hc i
  rw [hv', hd, ← tensorWordLp_cons U L i] at he
  exact he

variable [IsProbabilityMeasure (potentialMeasure φ)]
variable {κ : ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ),
    κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

include hκ hlower in
/-- Every compatible tensor has a global weighted L² primitive with all
ordered derivatives through order s, expressed by literal local weak tests. -/
theorem exists_iterated_tensorWeakDerivatives (s : ℕ)
    (F : CompatibleTensorHilbert (hφ.of_le (by simp)) s) :
    ∃ U : (k : ℕ) → OrderedTensorField φ k,
      U s = (F : OrderedTensorField φ s) ∧
      (∀ k, k ≤ s → ‖U k‖ ≤ (Real.sqrt κ⁻¹) ^ (s - k) * ‖F‖) ∧
      (∀ L : List (Fin n), L.length < s → ∀ i : Fin n,
        ∀ ψ : Space n → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        (∫ x, tensorWordLp U L x * coordinateDerivative ψ i x) =
          -(∫ x, tensorWordLp U (i :: L) x * ψ x)) ∧
      ∀ k, k < s → U k ∈ centeredCompatibleTensorSubspace (hφ.of_le (by simp)) k := by
  obtain ⟨U, htop, _, hcenter, hgraph, hnorm⟩ :=
    exists_iterated_compatibleTensorPrimitive hφ hκ hlower s F
  refine ⟨U, htop, hnorm, ?_, hcenter⟩
  intro L hL i ψ hψ hc
  exact tensorWordLp_weak_identity (hφ.of_le (by simp)) U hgraph L hL i hψ hc

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorWordLp_compact_product
#print axioms KLS.DeterministicBridgeIntegration.exists_iterated_tensorWeakDerivatives

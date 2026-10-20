import TensorExteriorHilbertOperators

/-! Exact representative changes for full distributional differential
graphs, and their actual finite weighted L² elements. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology LinearPMap
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ} {φ : Space n → ℝ}
variable {ι ρ σ : Type*} [Fintype ι] [Fintype ρ] [Fintype σ]

lemma HasWeakMatrixDerivative.congr_ae {A : ρ → Fin n → ι → ℝ}
    {f f' : ι → Space n → ℝ} {g g' : ρ → Space n → ℝ}
    (h : HasWeakMatrixDerivative A f g) (hf : ∀ j, f j =ᵐ[volume] f' j)
    (hg : ∀ a, g a =ᵐ[volume] g' a) : HasWeakMatrixDerivative A f' g' := by
  intro ψ hψ hc a
  calc
    _ = ∫ x, g a x * ψ x := integral_congr_ae ((hg a).symm.mono (fun x hx => by rw [hx]))
    _ = _ := h ψ hψ hc a
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      exact integral_congr_ae ((hf j).mono (fun x hx => congrArg (fun z : ℝ => z * coordinateDerivative ψ i x) hx))

lemma finiteMatrixLp_mem_weightedMatrixFiberGraph
    (hφ : ContDiff ℝ 1 φ) (A : ρ → Fin n → ι → ℝ)
    (C : Submodule ℝ (CenteredL2.Family (potentialMeasure φ) ι))
    (D : Submodule ℝ (CenteredL2.Family (potentialMeasure φ) ρ))
    {f : ι → Space n → ℝ} {g : ρ → Space n → ℝ}
    (hf : ∀ j, MemLp (f j) 2 (potentialMeasure φ))
    (hg : ∀ a, MemLp (g a) 2 (potentialMeasure φ))
    (hC : finiteMatrixLp f hf ∈ C) (hD : finiteMatrixLp g hg ∈ D)
    (hw : HasWeakMatrixDerivative A f g) :
    (⟨finiteMatrixLp f hf, hC⟩, ⟨finiteMatrixLp g hg, hD⟩) ∈ weightedMatrixFiberGraph hφ A C D := by
  rw [mem_weightedMatrixFiberGraph_iff]
  apply hw.congr_ae
  · intro j
    exact (volume_absolutelyContinuous_potentialMeasure hφ.continuous).ae_eq (hf j).coeFn_toLp.symm
  · intro a
    exact (volume_absolutelyContinuous_potentialMeasure hφ.continuous).ae_eq (hg a).coeFn_toLp.symm

lemma continuous_finiteMatrixLp_mem_constraint_iff_forall
    (hφ : Continuous φ) (C : σ → ι → ℝ)
    {f : ι → Space n → ℝ} (hf : ∀ j, MemLp (f j) 2 (potentialMeasure φ))
    (hfc : ∀ j, Continuous (f j)) :
    finiteMatrixLp f hf ∈ weightedMatrixConstraintSpace φ C ↔
      ∀ a x, (∑ j, C a j * f j x) = 0 := by
  rw [finiteMatrixLp_mem_constraint_iff]
  constructor
  · intro h a
    have ha : (fun x => ∑ j, C a j * f j x) =ᵐ[volume] 0 :=
      (volume_absolutelyContinuous_potentialMeasure hφ).ae_eq (h a)
    exact congrFun (MeasureTheory.Measure.eq_of_ae_eq ha
      (continuous_finsetSum Finset.univ (fun j _ => (hfc j).const_mul _)) continuous_zero)
  · exact fun h a => Eventually.of_forall (fun x => h a x)

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.finiteMatrixLp_mem_weightedMatrixFiberGraph

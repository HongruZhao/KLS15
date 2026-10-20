import WeightedMatrixFiberOperator

/-! Closed weighted L² realizations of actual finite linear fiber
constraints, with exact membership for genuine finite L² representatives. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology LinearPMap
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ} {φ : Space n → ℝ}
variable {ι σ : Type*} [Fintype ι] [Fintype σ]

def matrixFiberRow (C : σ → ι → ℝ) (a : σ) :
    CenteredL2.Family (potentialMeasure φ) ι →L[ℝ] Lp ℝ 2 (potentialMeasure φ) :=
  ∑ j : ι, C a j • (PiLp.proj 2 (fun _ : ι => Lp ℝ 2 (potentialMeasure φ)) j)

lemma matrixFiberRow_apply (C : σ → ι → ℝ) (a : σ)
    (F : CenteredL2.Family (potentialMeasure φ) ι) :
    matrixFiberRow C a F = ∑ j : ι, C a j • F j := by
  simp only [matrixFiberRow, _root_.sum_apply, _root_.smul_apply, PiLp.proj_apply]

def weightedMatrixConstraintSpace (φ : Space n → ℝ) (C : σ → ι → ℝ) :
    Submodule ℝ (CenteredL2.Family (potentialMeasure φ) ι) :=
  ⨅ a, LinearMap.ker (matrixFiberRow C a (φ := φ)).toLinearMap

lemma weightedMatrixConstraintSpace_isClosed (C : σ → ι → ℝ) :
    IsClosed (weightedMatrixConstraintSpace φ C : Set (CenteredL2.Family (potentialMeasure φ) ι)) := by
  simp only [weightedMatrixConstraintSpace, Submodule.coe_iInf]
  exact isClosed_iInter fun a => (matrixFiberRow C a).isClosed_ker

instance weightedMatrixConstraintSpace_complete (C : σ → ι → ℝ) :
    CompleteSpace (↥(weightedMatrixConstraintSpace φ C)) :=
  (weightedMatrixConstraintSpace_isClosed C).isComplete.completeSpace_coe

lemma mem_weightedMatrixConstraintSpace_iff (C : σ → ι → ℝ)
    (F : CenteredL2.Family (potentialMeasure φ) ι) :
    F ∈ weightedMatrixConstraintSpace φ C ↔ ∀ a, (∑ j : ι, C a j • F j) = 0 := by
  simp only [weightedMatrixConstraintSpace, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, matrixFiberRow_apply]

lemma finiteMatrixLp_mem_constraint_iff (C : σ → ι → ℝ)
    {f : ι → Space n → ℝ} (hf : ∀ j, MemLp (f j) 2 (potentialMeasure φ)) :
    finiteMatrixLp f hf ∈ weightedMatrixConstraintSpace φ C ↔
      ∀ a, (fun x => ∑ j : ι, C a j * f j x) =ᵐ[potentialMeasure φ] 0 := by
  rw [mem_weightedMatrixConstraintSpace_iff]
  have hae (a : σ) : ((∑ j : ι, C a j • finiteMatrixLp f hf j : Lp ℝ 2 (potentialMeasure φ)) :
      Space n → ℝ) =ᵐ[potentialMeasure φ] fun x => ∑ j : ι, C a j * f j x := by
    have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun j : ι => C a j • finiteMatrixLp f hf j)
    filter_upwards [hs, Filter.eventually_all.mpr (fun j : ι =>
      (Lp.coeFn_smul (C a j) (finiteMatrixLp f hf j)).and (hf j).coeFn_toLp)] with x hx hh
    rw [hx]
    apply Finset.sum_congr rfl
    intro j _
    exact (hh j).1.trans (congrArg (fun z : ℝ => C a j * z) (hh j).2)
  constructor
  · intro h a
    exact (hae a).symm.trans ((congrArg (fun z : Lp ℝ 2 (potentialMeasure φ) =>
      (z : Space n → ℝ)) (h a)) ▸ Lp.coeFn_zero ℝ 2 (potentialMeasure φ))
  · intro h a
    apply Lp.ext
    exact (hae a).trans ((h a).trans (Lp.coeFn_zero ℝ 2 (potentialMeasure φ)).symm)

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.finiteMatrixLp_mem_constraint_iff

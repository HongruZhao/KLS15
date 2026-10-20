import WeightedMatrixConstraintSpace

/-! Actual compact smooth density inside every finite constant linear
weighted L² fiber. It follows from the proved constraint-preserving matrix
cutoff/mollification core with a zero-dimensional output. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology LinearPMap
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ} {φ : Space n → ℝ}
variable {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq ι] [DecidableEq σ]

lemma finiteMatrixLp_coe_eq (F : CenteredL2.Family (potentialMeasure φ) ι) :
    finiteMatrixLp (fun j x => F j x) (fun j => Lp.memLp (F j)) = F := by
  apply PiLp.ext
  intro j
  change (Lp.memLp (F j)).toLp (F j) = F j
  exact Lp.toLp_coeFn (F j) (Lp.memLp (F j))

def compactSmoothFiberSet (φ : Space n → ℝ) (C : σ → ι → ℝ) :
    Set (↥(weightedMatrixConstraintSpace φ C)) :=
  {u | ∃ (f : ι → Space n → ℝ), (∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j)) ∧
    (∀ j, HasCompactSupport (f j)) ∧ ∃ (hf : ∀ j, MemLp (f j) 2 (potentialMeasure φ)),
      (u : CenteredL2.Family (potentialMeasure φ) ι) = finiteMatrixLp f hf}

/-- Fixed finite linear constraints impose no compact density assumption:
the approximation is proved for the entire actual weighted L² fiber. -/
theorem compactSmoothFiberSet_dense (hφ : Continuous φ) (C : σ → ι → ℝ) :
    Dense (compactSmoothFiberSet φ C) := by
  intro u
  rw [closure_subtype]
  let f : ι → Space n → ℝ := fun j x => (u : CenteredL2.Family (potentialMeasure φ) ι) j x
  have hf (j : ι) : MemLp (f j) 2 (potentialMeasure φ) := Lp.memLp _
  have he : finiteMatrixLp f hf = (u : CenteredL2.Family (potentialMeasure φ) ι) :=
    finiteMatrixLp_coe_eq _
  have hCμ := (finiteMatrixLp_mem_constraint_iff C hf).mp (he.symm ▸ u.property)
  have hC (a : σ) : (fun x => ∑ j, C a j * f j x) =ᵐ[volume] 0 :=
    (volume_absolutelyContinuous_potentialMeasure hφ).ae_eq (hCμ a)
  let A : Fin 0 → Fin n → ι → ℝ := fun a => Fin.elim0 a
  let B : Fin 0 → ι → Space n → ℝ := fun a => Fin.elim0 a
  let g : Fin 0 → Space n → ℝ := fun a => Fin.elim0 a
  have hg (a : Fin 0) : MemLp (g a) 2 (potentialMeasure φ) := Fin.elim0 a
  have hw : HasWeakMatrixFirstOrder A B f g := fun ψ hψ hc a => Fin.elim0 a
  have hcl := matrix_maximal_graph_mem_closure_compact_graph hφ A
    (fun a j => Fin.elim0 a) C hw hf hg hC
  have hfst : finiteMatrixLp f hf ∈ closure
      (Prod.fst '' compactMatrixGraphSet (φ := φ) A B C) :=
    mem_closure_image continuous_fst.continuousAt hcl
  rw [he] at hfst
  apply (closure_mono (s := Prod.fst '' compactMatrixGraphSet (φ := φ) A B C) ?_) hfst
  rintro v ⟨p, ⟨F, hF, hc, hFC, hFlp, hGlp, rfl⟩, rfl⟩
  have hm : finiteMatrixLp F hFlp ∈ weightedMatrixConstraintSpace φ C :=
    (finiteMatrixLp_mem_constraint_iff C hFlp).mpr
      (fun a => Eventually.of_forall (fun x => hFC a x))
  refine ⟨⟨finiteMatrixLp F hFlp, hm⟩, ?_, rfl⟩
  exact ⟨F, hF, hc, hFlp, rfl⟩

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.compactSmoothFiberSet_dense

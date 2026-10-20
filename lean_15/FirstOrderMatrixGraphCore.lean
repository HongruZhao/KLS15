import FirstOrderMatrixGlobalCutoff

/-! A proved compact core for the actual maximal first-order matrix graph,
with an arbitrary fixed finite linear input constraint. This is an analytic
graph approximation theorem, not a core-density assumption. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ} {ι ρ σ : Type*} [Fintype ι] [Fintype ρ] [Fintype σ]
  [DecidableEq ι] [DecidableEq ρ] [DecidableEq σ]

def finiteMatrixLp {μ : Measure (Space n)} (f : ι → Space n → ℝ)
    (hf : ∀ j, MemLp (f j) 2 μ) : CenteredL2.Family μ ι :=
  WithLp.toLp 2 (fun j => (hf j).toLp (f j))

lemma finiteMatrixLp_tendsto {μ : Measure (Space n)}
    {f : ℕ → ι → Space n → ℝ} {g : ι → Space n → ℝ}
    (hf : ∀ k j, MemLp (f k j) 2 μ) (hg : ∀ j, MemLp (g j) 2 μ)
    (h : ∀ j, Tendsto (fun k => eLpNorm (f k j - g j) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => finiteMatrixLp (f k) (hf k)) atTop (𝓝 (finiteMatrixLp g hg)) := by
  have ht : Tendsto (fun k => fun j => (hf k j).toLp (f k j)) atTop
      (𝓝 (fun j => (hg j).toLp (g j))) :=
    tendsto_pi_nhds.mpr (fun j => (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun k => f k j) (fun k => hf k j) (g j) (hg j)).mpr (h j))
  exact (PiLp.continuous_toLp (p := (2 : ENNReal))
    (fun _ : ι => Lp ℝ 2 μ)).tendsto (fun j => (hg j).toLp (g j)) |>.comp ht

lemma matrixFirstOrder_continuous (A : ρ → Fin n → ι → ℝ)
    {B : ρ → ι → Space n → ℝ} (hB : ∀ a j, Continuous (B a j))
    {f : ι → Space n → ℝ} (hf : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j)) (a : ρ) :
    Continuous (matrixFirstOrder A B f a) := by
  apply Continuous.add
  · apply continuous_finset_sum
    intro i _
    apply continuous_finset_sum
    intro j _
    exact (contDiff_coordinateDerivative (hf j) (m := 0) (by simp) i).continuous.const_mul (A a i j)
  · apply continuous_finset_sum
    intro j _
    exact (hB a j).mul (hf j).continuous

lemma matrixFirstOrder_hasCompactSupport (A : ρ → Fin n → ι → ℝ)
    (B : ρ → ι → Space n → ℝ) {f : ι → Space n → ℝ}
    (hc : ∀ j, HasCompactSupport (f j)) (a : ρ) :
    HasCompactSupport (matrixFirstOrder A B f a) := by
  apply HasCompactSupport.add
  · apply compactSupport_finsetSum Finset.univ
    intro i _
    apply compactSupport_finsetSum Finset.univ
    intro j _
    exact (hasCompactSupport_coordinateDerivative (hc j) i).mul_left
  · exact matrixZeroth_hasCompactSupport B hc a

def compactMatrixGraphSet {φ : Space n → ℝ}
    (A : ρ → Fin n → ι → ℝ) (B : ρ → ι → Space n → ℝ) (C : σ → ι → ℝ) :
    Set (CenteredL2.Family (potentialMeasure φ) ι × CenteredL2.Family (potentialMeasure φ) ρ) :=
  {p | ∃ (f : ι → Space n → ℝ),
    (∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j)) ∧ (∀ j, HasCompactSupport (f j)) ∧
      (∀ a x, (∑ j, C a j * f j x) = 0) ∧
        ∃ (hf : ∀ j, MemLp (f j) 2 (potentialMeasure φ))
          (hg : ∀ a, MemLp (matrixFirstOrder A B f a) 2 (potentialMeasure φ)),
          p = (finiteMatrixLp f hf, finiteMatrixLp (matrixFirstOrder A B f) hg)}

/-- Compact elements of the maximal combined weak domain admit an actual
smooth compact approximation in value and full first-order output. -/
theorem compact_matrix_graph_mem_closure_compact_graph {φ : Space n → ℝ}
    (hφ : Continuous φ) (A : ρ → Fin n → ι → ℝ)
    {B : ρ → ι → Space n → ℝ} (hB : ∀ a j, Continuous (B a j)) (C : σ → ι → ℝ)
    {f : ι → Space n → ℝ} {g : ρ → Space n → ℝ}
    (h : HasWeakMatrixFirstOrder A B f g)
    (hf : ∀ j, MemLp (f j) 2 (potentialMeasure φ)) (hfc : ∀ j, HasCompactSupport (f j))
    (hg : ∀ a, MemLp (g a) 2 (potentialMeasure φ)) (hgc : ∀ a, HasCompactSupport (g a))
    (hC : ∀ a, (fun x => ∑ j, C a j * f j x) =ᵐ[volume] 0) :
    (finiteMatrixLp f hf, finiteMatrixLp g hg) ∈ closure (compactMatrixGraphSet (φ := φ) A B C) := by
  have hloc (j : ι) := (memLp_volume_of_potentialMeasure_hasCompactSupport (hf j) hφ (hfc j)).locallyIntegrable
    (by norm_num)
  let fs (k : ℕ) (j : ι) := mollify k (f j)
  have hfs (k : ℕ) (j : ι) : ContDiff ℝ (⊤ : ℕ∞) (fs k j) := mollify_contDiff (hloc j) k
  have hcs (k : ℕ) (j : ι) : HasCompactSupport (fs k j) := hasCompactSupport_mollify (hfc j) k
  have hfm (k : ℕ) (j : ι) : MemLp (fs k j) 2 (potentialMeasure φ) :=
    memLp_of_continuous_hasCompactSupport hφ (hfs k j).continuous (hcs k j)
  have hgm (k : ℕ) (a : ρ) : MemLp (matrixFirstOrder A B (fs k) a) 2 (potentialMeasure φ) :=
    memLp_of_continuous_hasCompactSupport hφ (matrixFirstOrder_continuous A hB (hfs k) a)
      (matrixFirstOrder_hasCompactSupport A B (hcs k) a)
  have hF := finiteMatrixLp_tendsto hfm hf (fun j =>
    eLpNorm_compact_mollify_sub_potential_tendsto_zero hφ (hf j) (hfc j))
  have hG := finiteMatrixLp_tendsto hgm hg (fun a =>
    HasWeakMatrixFirstOrder.compact_smoothing hφ h hB hf hfc hg hgc a)
  apply isClosed_closure.mem_of_tendsto (hF.prodMk_nhds hG)
  exact Eventually.of_forall fun k => subset_closure
    ⟨fs k, hfs k, hcs k, mollify_preserves_linear_constraint C hloc hC k, hfm k, hgm k, rfl⟩

/-- Every element of the genuine maximal distributional first-order
matrix graph is approximated in its full graph norm by compact C∞ inputs
in the same fixed linear fiber. No graph-core premise is assumed. -/
theorem matrix_maximal_graph_mem_closure_compact_graph {φ : Space n → ℝ}
    (hφ : Continuous φ) (A : ρ → Fin n → ι → ℝ)
    {B : ρ → ι → Space n → ℝ} (hB : ∀ a j, Continuous (B a j)) (C : σ → ι → ℝ)
    {f : ι → Space n → ℝ} {g : ρ → Space n → ℝ}
    (h : HasWeakMatrixFirstOrder A B f g)
    (hf : ∀ j, MemLp (f j) 2 (potentialMeasure φ))
    (hg : ∀ a, MemLp (g a) 2 (potentialMeasure φ))
    (hC : ∀ a, (fun x => ∑ j, C a j * f j x) =ᵐ[volume] 0) :
    (finiteMatrixLp f hf, finiteMatrixLp g hg) ∈ closure (compactMatrixGraphSet (φ := φ) A B C) := by
  let fc (k : ℕ) (j : ι) (x : Space n) := smoothCutoff n k x * f j x
  let gc (k : ℕ) (a : ρ) (x : Space n) :=
    smoothCutoff n k x * g a x + matrixCutoffError A (smoothCutoff n k) f a x
  have hfm (k : ℕ) (j : ι) : MemLp (fc k j) 2 (potentialMeasure φ) := memLp_smoothCutoff_mul (hf j) k
  have hgm (k : ℕ) (a : ρ) : MemLp (gc k a) 2 (potentialMeasure φ) :=
    (memLp_smoothCutoff_mul (hg a) k).add
      (matrixCutoffError_memLp A (smoothCutoff_contDiff_top k) (smoothCutoff_hasCompactSupport k) hf a)
  have hfloc (j : ι) : LocallyIntegrable (f j) volume := locallyIntegrable_of_memLp_two_on_compacts
    (fun K hK => KLS.MemLp.restrict_volume_of_potentialMeasure (hf j) hφ hK)
  have hpre (a : ρ) := matrixFirstOrder_principal_locallyIntegrable hφ hB hf hg a
  have hin (k : ℕ) : (finiteMatrixLp (fc k) (hfm k), finiteMatrixLp (gc k) (hgm k)) ∈
      closure (compactMatrixGraphSet (φ := φ) A B C) := by
    apply compact_matrix_graph_mem_closure_compact_graph hφ A hB C
      (HasWeakMatrixFirstOrder.cutoff h hfloc hpre (smoothCutoff_contDiff_top k)
        (smoothCutoff_hasCompactSupport k)) (hfm k)
      (fun j => (smoothCutoff_hasCompactSupport k).mul_right) (hgm k)
      (fun a => ((smoothCutoff_hasCompactSupport k).mul_right).add
        (matrixCutoffError_hasCompactSupport A (smoothCutoff_hasCompactSupport k) f a))
    exact cutoff_preserves_linear_constraint C hC (smoothCutoff n k)
  have hF := finiteMatrixLp_tendsto hfm hf (fun j => eLpNorm_smoothCutoff_mul_sub_tendsto_zero (hf j))
  have hG := finiteMatrixLp_tendsto hgm hg (fun a => eLpNorm_matrix_graph_cutoff_tendsto_zero A hf hg a)
  exact isClosed_closure.mem_of_tendsto (hF.prodMk_nhds hG) (Eventually.of_forall hin)

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.compact_matrix_graph_mem_closure_compact_graph
#print axioms KLS.DeterministicBridgeIntegration.matrix_maximal_graph_mem_closure_compact_graph

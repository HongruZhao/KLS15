import FirstOrderMatrixDrift

/-! Global weighted graph convergence of the actual expanding cutoffs for
constant-principal-matrix first-order domains with continuous drift. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ} {ι ρ : Type*} [Fintype ι] [Fintype ρ]
  [DecidableEq ι] [DecidableEq ρ]

lemma matrixFirstOrder_principal_locallyIntegrable {φ : Space n → ℝ}
    (hφ : Continuous φ) {B : ρ → ι → Space n → ℝ}
    {f : ι → Space n → ℝ} {g : ρ → Space n → ℝ}
    (hB : ∀ a j, Continuous (B a j))
    (hf : ∀ j, MemLp (f j) 2 (potentialMeasure φ))
    (hg : ∀ a, MemLp (g a) 2 (potentialMeasure φ)) (a : ρ) :
    LocallyIntegrable (fun x => g a x - matrixZeroth B f a x) volume := by
  apply locallyIntegrable_of_memLp_two_on_compacts
  intro K hK
  apply MemLp.sub (KLS.MemLp.restrict_volume_of_potentialMeasure (hg a) hφ hK)
  apply memLp_finsetSum Finset.univ
  intro j _
  simpa only [mul_comm] using memLp_mul_continuous_on_compact hK
    (KLS.MemLp.restrict_volume_of_potentialMeasure (hf j) hφ hK) (hB a j)

lemma matrixCutoffError_memLp {φ χ : Space n → ℝ}
    (A : ρ → Fin n → ι → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) {f : ι → Space n → ℝ}
    (hf : ∀ j, MemLp (f j) 2 (potentialMeasure φ)) (a : ρ) :
    MemLp (matrixCutoffError A χ f a) 2 (potentialMeasure φ) := by
  apply memLp_finsetSum Finset.univ
  intro i _
  apply memLp_finsetSum Finset.univ
  intro j _
  exact (((contDiff_coordinateDerivative hχ (m := 0) (by simp) i).continuous.const_mul
    (A a i j)).memLp_top_of_hasCompactSupport
      (hasCompactSupport_coordinateDerivative hc i).mul_left (potentialMeasure φ)).mul (hf j)

lemma matrixCutoffError_hasCompactSupport (A : ρ → Fin n → ι → ℝ)
    {χ : Space n → ℝ} (hc : HasCompactSupport χ) (f : ι → Space n → ℝ) (a : ρ) :
    HasCompactSupport (matrixCutoffError A χ f a) := by
  apply compactSupport_finsetSum Finset.univ
  intro i _
  apply compactSupport_finsetSum Finset.univ
  intro j _
  exact ((hasCompactSupport_coordinateDerivative hc i).mul_left).mul_right

lemma eLpNorm_smoothCutoff_coordinate_mul_tendsto_zero {μ : Measure (Space n)}
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (i : Fin n) :
    Tendsto (fun k => eLpNorm
      (fun x => coordinateDerivative (smoothCutoff n k) i x * f x) 2 μ) atTop (𝓝 0) := by
  obtain ⟨K, hK, hb⟩ := smoothCutoff_gradient_bound (n := n)
  have hKu (k : ℕ) (x : Space n) : ‖coordinateDerivative (smoothCutoff n k) i x‖ ≤ K := by
    exact ((norm_coordinateDerivative_le _ i x).trans (hb k x)).trans
      (mul_le_of_le_one_left hK (cutoffScale_le_one k))
  have hm (k : ℕ) : AEStronglyMeasurable
      (fun x => coordinateDerivative (smoothCutoff n k) i x * f x) μ :=
    (contDiff_coordinateDerivative (smoothCutoff_contDiff_top k) (m := 0) (by simp) i).continuous.aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  apply eLpNorm_tendsto_zero_of_L2_pointwise_bound (hf.norm.const_mul K) hm
  · intro k x
    rw [norm_mul, Real.norm_eq_abs (K * ‖f x‖), abs_of_nonneg (mul_nonneg hK (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_right (hKu k x) (norm_nonneg _)
  · intro x
    simpa only [zero_mul] using (smoothCutoff_coordinateDerivative_tendsto_zero i x).mul_const (f x)

theorem eLpNorm_matrixCutoffError_smoothCutoff_tendsto_zero {μ : Measure (Space n)}
    (A : ρ → Fin n → ι → ℝ) {f : ι → Space n → ℝ}
    (hf : ∀ j, MemLp (f j) 2 μ) (a : ρ) :
    Tendsto (fun k => eLpNorm (matrixCutoffError A (smoothCutoff n k) f a) 2 μ)
      atTop (𝓝 0) := by
  have ht (i : Fin n) (j : ι) : Tendsto
      (fun k => eLpNorm ((fun x => A a i j * coordinateDerivative (smoothCutoff n k) i x * f j x) - 0)
        2 μ) atTop (𝓝 0) := by
    have he := eLpNorm_smoothCutoff_coordinate_mul_tendsto_zero ((hf j).const_mul (A a i j)) i
    convert he using 1
    funext k
    congr 1
    funext x
    simp only [Pi.sub_apply, Pi.zero_apply]
    ring
  have hs := matrix_l2_sum_limit Finset.univ (fun i _ =>
    matrix_l2_sum_limit Finset.univ (fun j _ => ht i j))
  simp only [Finset.sum_const_zero, sub_zero] at hs
  convert hs using 1
  funext k
  congr 1
  funext x
  simp only [matrixCutoffError, Finset.sum_apply]

theorem eLpNorm_matrix_graph_cutoff_tendsto_zero {μ : Measure (Space n)}
    (A : ρ → Fin n → ι → ℝ) {f : ι → Space n → ℝ} {g : ρ → Space n → ℝ}
    (hf : ∀ j, MemLp (f j) 2 μ) (hg : ∀ a, MemLp (g a) 2 μ) (a : ρ) :
    Tendsto (fun k => eLpNorm
      (fun x => smoothCutoff n k x * g a x + matrixCutoffError A (smoothCutoff n k) f a x - g a x)
        2 μ) atTop (𝓝 0) := by
  have he : Tendsto (fun k => eLpNorm
      (matrixCutoffError A (smoothCutoff n k) f a - 0) 2 μ) atTop (𝓝 0) := by
    simpa only [sub_zero] using eLpNorm_matrixCutoffError_smoothCutoff_tendsto_zero A hf a
  have ht := matrix_l2_add_limit (eLpNorm_smoothCutoff_mul_sub_tendsto_zero (hg a)) he
  convert ht using 1
  funext k
  congr 1
  funext x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply, add_zero]

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.matrixFirstOrder_principal_locallyIntegrable
#print axioms KLS.DeterministicBridgeIntegration.eLpNorm_matrix_graph_cutoff_tendsto_zero

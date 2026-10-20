import KLSConstantImprovement.ActualSourceGlobalCurvature405
import KLSConstantImprovement.ActualWeakCanonicalMetricCutoffs
import KLS.MatrixEntryLpProducts

/-! Global L1 domains of every actual source curvature/third-Gram entry.
Positivity and the proved diagonal integrability pay the off-diagonal entries.
The target part is actually bounded on the bounded gradient range.
-/
noncomputable section
open MeasureTheory Matrix Set Filter
open scoped BigOperators ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceCurvatureDomains405
open KLS ActualBoundedCanonicalSource ActualSourceHessianEvolution405 ActualSourceGlobalCurvature405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem posSemidef_abs_entry_le_diagonal_sum (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (i j : Fin n) : |A i j| ≤ A i i + A j j := by
  have hp := hA.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
  have hm := hA.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct,
    sub_dotProduct, dotProduct_add, dotProduct_sub, Matrix.mulVec_single_one,
    single_one_dotProduct] at hp hm
  change 0 ≤ A i i + A j i + (A i j + A j j) at hp
  change 0 ≤ A i i - A j i - (A i j - A j j) at hm
  have hsym : A j i = A i j := hA.isHermitian.isSymm.apply i j
  have hi : 0 ≤ A i i := hA.diag_nonneg
  have hj : 0 ≤ A j j := hA.diag_nonneg
  apply abs_le.mpr
  constructor <;> linarith

theorem actual_connection_curvature_entry_measurable (d : SourceData μ) (i j : Fin n) :
    AEStronglyMeasurable (fun x => sourceConnectionCurvature d x i j)
      (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  obtain ⟨x₀, _, hc, _, hp, _, _, _, _⟩ := d.exists_metric_energy_cutoffs
  let χ : ℕ → Space n → ℝ := hessianMetricCutoffSequence d.potential x₀
  have hHi : Integrable (fun x => coordinateHessian d.potential x i j)
      (potentialMeasure d.potential) := (d.hessian_entry_memLp i j 1).integrable le_rfl
  have hχHi (k : ℕ) : Integrable (fun x => χ k x * coordinateHessian d.potential x i j)
      (potentialMeasure d.potential) := by
    apply hHi.bdd_mul (hc k).1.continuous.aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg ((hc k).2.2 x).1]
      exact ((hc k).2.2 x).2
  have hχCi (k : ℕ) : Integrable (fun x => χ k x * sourceConnectionCurvature d x i j)
      (potentialMeasure d.potential) := by
    have he := actual_compact_hessian_evolution d (hc k).1 (hc k).2.1 i j
    apply (he.2.1.add (hχHi k)).congr
    exact Eventually.of_forall fun x => by
      change (-coordinateHessian d.potential x i j + sourceConnectionCurvature d x i j) * χ k x +
        χ k x * coordinateHessian d.potential x i j = χ k x * sourceConnectionCurvature d x i j
      ring
  exact aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hχCi k).aestronglyMeasurable)
    (Eventually.of_forall fun x => by
      simpa only [one_mul] using (hp x).mul_const (sourceConnectionCurvature d x i j))

theorem actual_connection_curvature_entry_integrable (d : SourceData μ) (i j : Fin n) :
    Integrable (fun x => sourceConnectionCurvature d x i j) (potentialMeasure d.potential) := by
  apply ((actual_connection_curvature_diagonal_integrable d i).1.add
    (actual_connection_curvature_diagonal_integrable d j).1).mono'
      (actual_connection_curvature_entry_measurable d i j)
  filter_upwards [actual_source_connection_curvature_positive d] with x hx
  rw [Real.norm_eq_abs]
  exact posSemidef_abs_entry_le_diagonal_sum _ hx i j

def sourceTargetCurvature (d : SourceData μ) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  coordinateHessian d.potential x * coordinateHessian d.targetPotential (gradient d.potential x) *
    coordinateHessian d.potential x

theorem actual_target_curvature_entry_memLp_top (d : SourceData μ) (i j : Fin n) :
    MemLp (fun x => sourceTargetCurvature d x i j) ∞ (potentialMeasure d.potential) := by
  have hV2 : ContDiff ℝ 2 d.targetPotential := d.target_smooth.of_le (by simp)
  have hB (a b : Fin n) : MemLp
      (fun x => coordinateHessian d.targetPotential (gradient d.potential x) a b) ∞
      (potentialMeasure d.potential) :=
    d.continuous_comp_gradient_memLp
      (contDiff_coordinateHessian hV2 (m := 0) (by norm_num) a b).continuous ∞
  have hM : ∀ a b, MemLp (fun x => (coordinateHessian d.potential x *
      coordinateHessian d.targetPotential (gradient d.potential x)) a b) ∞
      (potentialMeasure d.potential) := memLp_matrix_mul_entries (p := ∞) (q := ∞) (r := ∞)
        (fun a b => d.hessian_entry_memLp a b ∞) hB
  exact memLp_matrix_mul_entries (p := ∞) (q := ∞) (r := ∞) hM (fun a b => d.hessian_entry_memLp a b ∞) i j

theorem actual_third_gram_entry_integrable (d : SourceData μ) (i j : Fin n) :
    Integrable (fun x => matrixTraceGram (coordinateHessian d.potential x)⁻¹
      (sourceThirdMatrix d x) i j) (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hi := (actual_connection_curvature_entry_integrable d i j).sub
    ((actual_target_curvature_entry_memLp_top d i j).integrable (by simp))
  convert hi using 1
  funext x
  simp only [sourceConnectionCurvature, sourceTargetCurvature, Matrix.add_apply,
    Pi.sub_apply, add_sub_cancel_left]

end KLSConstantImprovement.ActualSourceCurvatureDomains405
#print axioms KLSConstantImprovement.ActualSourceCurvatureDomains405.actual_connection_curvature_entry_integrable
#print axioms KLSConstantImprovement.ActualSourceCurvatureDomains405.actual_target_curvature_entry_memLp_top
#print axioms KLSConstantImprovement.ActualSourceCurvatureDomains405.actual_third_gram_entry_integrable

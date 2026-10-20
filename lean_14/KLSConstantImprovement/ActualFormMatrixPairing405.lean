import KLSConstantImprovement.ActualSourceUnfilteredDeficit405
import KLSConstantImprovement.ActualMetricMatrixCongruence405

/-! Finite matrices of genuine scalar canonical forms. Their energy
and value pairings are literal integrable matrix entry contractions. -/
noncomputable section
open MeasureTheory Matrix InnerProductSpace Filter
open scoped BigOperators
namespace KLSConstantImprovement.ActualFormMatrixPairing405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualQuarticCompression405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

def formValueMatrix (d : SourceData μ) (U : Fin n → Fin n → CanonicalMetricH1 d.potential)
    (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => canonicalMetricValue d.potential (U i j) x

def formGradientMatrix (d : SourceData μ) (U : Fin n → Fin n → CanonicalMetricH1 d.potential)
    (r : Fin n) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => canonicalMetricGradient d.potential r (U i j) x

theorem actual_form_matrix_value_pair (d : SourceData μ)
    (U V : Fin n → Fin n → CanonicalMetricH1 d.potential) :
    (∑ i, ∑ j, inner ℝ (canonicalMetricValue d.potential (U i j))
      (canonicalMetricValue d.potential (V i j))) =
      ∫ x, entryPair (formValueMatrix d U x) (formValueMatrix d V x) ∂potentialMeasure d.potential := by
  have he (i j : Fin n) : inner ℝ (canonicalMetricValue d.potential (U i j))
      (canonicalMetricValue d.potential (V i j)) =
      ∫ x, canonicalMetricValue d.potential (U i j) x * canonicalMetricValue d.potential (V i j) x
        ∂potentialMeasure d.potential := by
    rw [L2.inner_def]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by simp only [RCLike.inner_apply, conj_trivial]; ring
  have hi (i j : Fin n) : Integrable (fun x =>
      canonicalMetricValue d.potential (U i j) x * canonicalMetricValue d.potential (V i j) x)
      (potentialMeasure d.potential) :=
    (Lp.memLp (canonicalMetricValue d.potential (U i j))).integrable_mul
      (Lp.memLp (canonicalMetricValue d.potential (V i j)))
  simp_rw [he]
  unfold entryPair formValueMatrix
  simp only [Matrix.of_apply]
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ fun j _ => hi i j)]
  exact Finset.sum_congr rfl fun i _ => (integral_finsetSum Finset.univ (fun j _ => hi i j)).symm

theorem actual_form_matrix_energy_pair (d : SourceData μ)
    (U V : Fin n → Fin n → CanonicalMetricH1 d.potential) :
    (∑ i, ∑ j, canonicalMetricEnergy d.potential (U i j) (V i j)) =
      ∫ x, ∑ r, entryPair (formGradientMatrix d U r x) (formGradientMatrix d V r x)
        ∂potentialMeasure d.potential := by
  have he (i j r : Fin n) : inner ℝ (canonicalMetricGradient d.potential r (U i j))
      (canonicalMetricGradient d.potential r (V i j)) =
      ∫ x, canonicalMetricGradient d.potential r (U i j) x * canonicalMetricGradient d.potential r (V i j) x
        ∂potentialMeasure d.potential := by
    rw [L2.inner_def]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by simp only [RCLike.inner_apply, conj_trivial]; ring
  have hi (r i j : Fin n) : Integrable (fun x =>
      canonicalMetricGradient d.potential r (U i j) x * canonicalMetricGradient d.potential r (V i j) x)
      (potentialMeasure d.potential) :=
    (Lp.memLp (canonicalMetricGradient d.potential r (U i j))).integrable_mul
      (Lp.memLp (canonicalMetricGradient d.potential r (V i j)))
  simp_rw [canonicalMetricEnergy_apply, he]
  unfold entryPair formGradientMatrix
  simp only [Matrix.of_apply]
  rw [integral_finsetSum Finset.univ (fun r _ => integrable_finsetSum Finset.univ fun i _ =>
    integrable_finsetSum Finset.univ fun j _ => hi r i j)]
  simp_rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ fun j _ => hi _ i j),
    integral_finsetSum Finset.univ (fun j _ => hi _ _ j)]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

end KLSConstantImprovement.ActualFormMatrixPairing405
#print axioms KLSConstantImprovement.ActualFormMatrixPairing405.actual_form_matrix_value_pair
#print axioms KLSConstantImprovement.ActualFormMatrixPairing405.actual_form_matrix_energy_pair

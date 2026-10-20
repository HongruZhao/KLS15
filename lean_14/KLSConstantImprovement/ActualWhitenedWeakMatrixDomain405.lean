import KLSConstantImprovement.ActualSourceNaturalWhitenedHessian405
import KLSConstantImprovement.ActualWhitenedJacobianEnergy405

/-! Actual global L2 coordinates from genuine matrix energy integrals.
Only local L2 and the displayed integral are required; no classical
matrix derivative or strong operator domain is inferred. This applies
to source third contractions and H-compatible weak Jacobians. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualWhitenedWeakMatrixDomain405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualWeakCanonicalMetricOrdinaryGraph ActualSourceMetricFaithfulness405
open ActualSourceLimitFluxDomains405 ActualCompatibleConnectionYoung405
open ActualWhitenedJacobianEnergy405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {n : ℕ} {μ : Measure (Space n)}

theorem matrix_entry_memLp_of_integrable_frobenius (d : SourceData μ)
    (A : Space n → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j E, IsCompact E → MemLp (fun x => A x i j) 2 (volume.restrict E))
    (hE : Integrable (fun x => matrixFrobeniusSq (A x)) (potentialMeasure d.potential))
    (i j : Fin n) : MemLp (fun x => A x i j) 2 (potentialMeasure d.potential) := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  have hm : AEStronglyMeasurable (fun x => A x i j) (potentialMeasure d.potential) :=
    (locallyIntegrable_of_memLp_two_on_compacts (hA i j)).aestronglyMeasurable.mono_ac hac
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply hE.mono' (hm.pow 2)
  exact Eventually.of_forall fun x => by
    change ‖A x i j ^ 2‖ ≤ matrixFrobeniusSq (A x)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hrow : A x i j ^ 2 ≤ ∑ b : Fin n, A x i b ^ 2 :=
      Finset.single_le_sum (fun b _ => sq_nonneg (A x i b)) (Finset.mem_univ j)
    have hall : (∑ b : Fin n, A x i b ^ 2) ≤ matrixFrobeniusSq (A x) :=
      Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg (A x a b)) (Finset.mem_univ i)
    exact hrow.trans hall

def sourceWhitenedMatrix (d : SourceData μ) (A : Space n → Matrix (Fin n) (Fin n) ℝ)
    (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  canonicalMetricRoot d.potential x * A x * canonicalMetricRoot d.potential x

theorem sourceWhitenedMatrix_local_L2 (d : SourceData μ)
    (A : Space n → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j E, IsCompact E → MemLp (fun x => A x i j) 2 (volume.restrict E))
    (i j : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (fun x => sourceWhitenedMatrix d A x i j) 2 (volume.restrict E) := by
  have hR (a b : Fin n) : MemLp (fun x => canonicalMetricRoot d.potential x a b) ∞ (volume.restrict E) :=
    actualRoot_entry_top_on_compact d hE a b
  have hRA (a b : Fin n) : MemLp (fun x => (canonicalMetricRoot d.potential x * A x) a b)
      2 (volume.restrict E) :=
    memLp_matrix_mul_entries (p := ∞) (q := 2) (r := 2) hR (fun a b => hA a b E hE) a b
  exact memLp_matrix_mul_entries (p := 2) (q := ∞) (r := 2) hRA hR i j

theorem sourceWhitenedMatrix_entry_memLp (d : SourceData μ)
    (A : Space n → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j E, IsCompact E → MemLp (fun x => A x i j) 2 (volume.restrict E))
    (hs : ∀ᵐ x ∂potentialMeasure d.potential, (A x).IsSymm)
    (hE : Integrable (fun x => ((coordinateHessian d.potential x)⁻¹ * A x *
      (coordinateHessian d.potential x)⁻¹ * A x).trace) (potentialMeasure d.potential))
    (i j : Fin n) : MemLp (fun x => sourceWhitenedMatrix d A x i j) 2 (potentialMeasure d.potential) := by
  have he : (fun x => ((coordinateHessian d.potential x)⁻¹ * A x *
      (coordinateHessian d.potential x)⁻¹ * A x).trace) =ᵐ[potentialMeasure d.potential]
      fun x => matrixFrobeniusSq (sourceWhitenedMatrix d A x) := by
    filter_upwards [d.hessian_ae_source, hs] with x hx hxs
    exact (whitened_connection_square (coordinateHessian d.potential x) (A x) hx.1 hxs).symm
  exact matrix_entry_memLp_of_integrable_frobenius d (sourceWhitenedMatrix d A)
    (sourceWhitenedMatrix_local_L2 d A hA) (hE.congr he) i j

def sourceWhitenedJacobian (d : SourceData μ) (D : Space n → Matrix (Fin n) (Fin n) ℝ)
    (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  canonicalMetricUnroot d.potential x * D x * canonicalMetricRoot d.potential x

theorem sourceWhitenedJacobian_local_L2 (d : SourceData μ)
    (D : Space n → Matrix (Fin n) (Fin n) ℝ)
    (hD : ∀ i j E, IsCompact E → MemLp (fun x => D x i j) 2 (volume.restrict E))
    (i j : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (fun x => sourceWhitenedJacobian d D x i j) 2 (volume.restrict E) := by
  have hS (a b : Fin n) : MemLp (fun x => canonicalMetricUnroot d.potential x a b) ∞ (volume.restrict E) :=
    KLS.MemLp.restrict_volume_of_potentialMeasure (actualUnroot_entry_memLp_top d a b) d.source_C1.continuous hE
  have hR (a b : Fin n) : MemLp (fun x => canonicalMetricRoot d.potential x a b) ∞ (volume.restrict E) :=
    actualRoot_entry_top_on_compact d hE a b
  have hSD (a b : Fin n) : MemLp (fun x => (canonicalMetricUnroot d.potential x * D x) a b)
      2 (volume.restrict E) :=
    memLp_matrix_mul_entries (p := ∞) (q := 2) (r := 2) hS (fun a b => hD a b E hE) a b
  exact memLp_matrix_mul_entries (p := 2) (q := ∞) (r := 2) hSD hR i j

theorem sourceWhitenedJacobian_entry_memLp (d : SourceData μ)
    (D : Space n → Matrix (Fin n) (Fin n) ℝ)
    (hD : ∀ i j E, IsCompact E → MemLp (fun x => D x i j) 2 (volume.restrict E))
    (hc : ∀ᵐ x ∂potentialMeasure d.potential, (coordinateHessian d.potential x * D x).IsSymm)
    (hE : Integrable (fun x => (D x * D x).trace) (potentialMeasure d.potential))
    (i j : Fin n) : MemLp (fun x => sourceWhitenedJacobian d D x i j) 2 (potentialMeasure d.potential) := by
  have he : (fun x => (D x * D x).trace) =ᵐ[potentialMeasure d.potential]
      fun x => matrixFrobeniusSq (sourceWhitenedJacobian d D x) := by
    filter_upwards [d.hessian_ae_source, hc] with x hx hxs
    exact (whitenedJacobian_frobenius (coordinateHessian d.potential x) (D x) hx.1 hxs).symm
  exact matrix_entry_memLp_of_integrable_frobenius d (sourceWhitenedJacobian d D)
    (sourceWhitenedJacobian_local_L2 d D hD) (hE.congr he) i j

end KLSConstantImprovement.ActualWhitenedWeakMatrixDomain405

#print axioms KLSConstantImprovement.ActualWhitenedWeakMatrixDomain405.matrix_entry_memLp_of_integrable_frobenius
#print axioms KLSConstantImprovement.ActualWhitenedWeakMatrixDomain405.sourceWhitenedMatrix_entry_memLp
#print axioms KLSConstantImprovement.ActualWhitenedWeakMatrixDomain405.sourceWhitenedJacobian_entry_memLp

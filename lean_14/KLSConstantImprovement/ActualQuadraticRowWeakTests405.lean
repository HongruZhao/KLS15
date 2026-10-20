import KLSConstantImprovement.ActualQuadraticRowEquation405
import KLSConstantImprovement.ActualPotentialWeakTests405

/-! Actual differentiated quadratic rows accept genuine bounded compact
raw H1 tests. This is the proved row equation, rather than a production
PDE input; every compact coefficient pairing is integrable. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualQuadraticRowWeakTests405
open KLS ActualBoundedCanonicalSource ActualSourceNaturalGaffney405 ActualSourceQuadraticEta405
open ActualQuadraticResponseField405 ActualQuadraticRowEquation405 ActualPotentialWeakTests405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {n : ℕ} {μ : Measure (Space n)}

def quadraticRowDrift (d : SourceData μ) (B : Matrix (Fin n) (Fin n) ℝ)
    (j : Fin n) (x : Space n) : ℝ :=
  quadraticDatumRawDerivative d B j x - ∑ i : Fin n,
    coordinateHessian d.potential x i j * naturalCanonicalFlux d (quadraticSourceDatum d B) i x

theorem quadraticRowDrift_local_L2 (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (B : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
    MemLp (quadraticRowDrift d B j) 2 (volume.restrict E) := by
  have hg := KLS.MemLp.restrict_volume_of_potentialMeasure
    (quadraticDatumRawDerivative_memLp d B j) d.source_C1.continuous hE
  have hH (i : Fin n) : MemLp (fun x => coordinateHessian d.potential x i j) ∞
      (volume.restrict E) := KLS.MemLp.restrict_volume_of_potentialMeasure
        (d.hessian_entry_memLp i j ∞) d.source_C1.continuous hE
  exact hg.sub (memLp_finsetSum Finset.univ fun i _ =>
    (hH i).mul (quadratic_row_flux_local_L2 d hn hμ B i hE))

theorem actual_quadratic_row_drift_compact_test (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (B : Matrix (Fin n) (Fin n) ℝ) (j : Fin n)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    (∑ i : Fin n, ∫ x, quadraticFluxJacobian d hn hμ B i j x * coordinateDerivative ψ i x
      ∂potentialMeasure d.potential) =
      ∫ x, quadraticRowDrift d B j x * ψ x ∂potentialMeasure d.potential := by
  have he := actual_quadratic_row_differentiated_compact_equation d hn hμ B j
    (hψ.of_le (by norm_num)) hc
  have hHi (i : Fin n) : LocallyIntegrable (fun x => coordinateHessian d.potential x i j *
      naturalCanonicalFlux d (quadraticSourceDatum d B) i x) volume :=
    locallyIntegrable_of_memLp_two_on_compacts fun E hE =>
      (KLS.MemLp.restrict_volume_of_potentialMeasure (d.hessian_entry_memLp i j ∞)
        d.source_C1.continuous hE).mul (quadratic_row_flux_local_L2 d hn hμ B i hE)
  have hHiψ (i : Fin n) : Integrable (fun x => coordinateHessian d.potential x i j *
      naturalCanonicalFlux d (quadraticSourceDatum d B) i x * ψ x) (potentialMeasure d.potential) :=
    integrable_raw_mul_compact_potential d.source_C1.continuous (hHi i) hψ.continuous hc
  have hDbψ : Integrable (fun x => quadraticDatumRawDerivative d B j x * ψ x)
      (potentialMeasure d.potential) :=
    (quadraticDatumRawDerivative_memLp d B j).integrable_mul
      (memLp_of_continuous_hasCompactSupport d.source_C1.continuous hψ.continuous hc)
  have hsumE : (fun x => (∑ i : Fin n, coordinateHessian d.potential x i j *
      naturalCanonicalFlux d (quadraticSourceDatum d B) i x) * ψ x) =
      fun x => ∑ i : Fin n, coordinateHessian d.potential x i j *
        naturalCanonicalFlux d (quadraticSourceDatum d B) i x * ψ x := by
    funext x
    rw [Finset.sum_mul]
  have hsumψ : Integrable (fun x => (∑ i : Fin n, coordinateHessian d.potential x i j *
      naturalCanonicalFlux d (quadraticSourceDatum d B) i x) * ψ x) (potentialMeasure d.potential) := by
    rw [hsumE]
    exact integrable_finsetSum Finset.univ fun i _ => hHiψ i
  have hr : (∫ x, quadraticRowDrift d B j x * ψ x ∂potentialMeasure d.potential) =
      (∫ x, quadraticDatumRawDerivative d B j x * ψ x ∂potentialMeasure d.potential) -
      ∑ i : Fin n, ∫ x, coordinateHessian d.potential x i j *
        naturalCanonicalFlux d (quadraticSourceDatum d B) i x * ψ x ∂potentialMeasure d.potential := by
    calc
      _ = (∫ x, quadraticDatumRawDerivative d B j x * ψ x ∂potentialMeasure d.potential) -
          ∫ x, (∑ i : Fin n, coordinateHessian d.potential x i j *
            naturalCanonicalFlux d (quadraticSourceDatum d B) i x) * ψ x
              ∂potentialMeasure d.potential := by
        rw [← integral_sub hDbψ hsumψ]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by dsimp only [quadraticRowDrift]; ring
      _ = _ := by rw [hsumE, integral_finsetSum Finset.univ (fun i _ => hHiψ i)]
  rw [hr]
  linarith

theorem actual_quadratic_row_compact_rawH1_test (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (B : Matrix (Fin n) (Fin n) ℝ) (j : Fin n)
    {f : Space n → ℝ} {F : Fin n → Space n → ℝ}
    (hf : ∀ E, IsCompact E → MemLp f 2 (volume.restrict E))
    (hc : HasCompactSupport f) {C : ℝ} (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ C)
    (hFloc : ∀ i E, IsCompact E → MemLp (F i) 2 (volume.restrict E))
    (hF : ∀ i, HasLocalWeakCoordinateDerivative f (F i) i) :
    (∀ i, Integrable (fun x => quadraticFluxJacobian d hn hμ B i j x * F i x)
      (potentialMeasure d.potential)) ∧
      Integrable (fun x => quadraticRowDrift d B j x * f x) (potentialMeasure d.potential) ∧
      (∑ i : Fin n, ∫ x, quadraticFluxJacobian d hn hμ B i j x * F i x
        ∂potentialMeasure d.potential) =
        ∫ x, quadraticRowDrift d B j x * f x ∂potentialMeasure d.potential :=
  potential_divergence_bounded_compact_H1_test d
    (fun i _ hE => quadratic_flux_jacobian_local_L2 d hn hμ B i j hE)
    (quadraticRowDrift_local_L2 d hn hμ B j)
    (fun _ hψ hψc => actual_quadratic_row_drift_compact_test d hn hμ B j hψ hψc)
    hf hc hbound hFloc hF

end KLSConstantImprovement.ActualQuadraticRowWeakTests405

#print axioms KLSConstantImprovement.ActualQuadraticRowWeakTests405.actual_quadratic_row_drift_compact_test
#print axioms KLSConstantImprovement.ActualQuadraticRowWeakTests405.actual_quadratic_row_compact_rawH1_test

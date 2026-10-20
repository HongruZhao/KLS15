import KLSConstantImprovement.ActualQuadraticResponseField405
import KLSConstantImprovement.ActualSourceRegularizedFluxDivergence405
import KLS.LocalL2CompactPairings

/-! Actual source adjoints of natural Poisson fluxes.  Local L2, rather
than an unproved global Euclidean flux bound, suffices for separation.
The final quadratic theorem uses the actual Gaffney-chosen derivative. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff NNReal ENNReal
namespace KLSConstantImprovement.ActualNaturalFluxAdjoint405
open KLS ActualBoundedCanonicalSource ActualSourceNaturalGaffney405
open ActualCompactSourceVectorBochner ActualCompactWeakSourceVectorBochner
open ActualCompactWeakSourceVectorSquare ActualWeakSourceCompactVectorBochner
open ActualSourceRegularizedLocalEquation405 ActualSourceRegularizedFluxDivergence405
open ActualQuadraticResponseField405 ActualSourceQuadraticEta405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {n : ℕ} {μ : Measure (Space n)}

theorem raw_vector_source_adjoint_local_compact_pair (d : SourceData μ)
    (u : Fin n → Space n → ℝ) (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (u i) 2 (volume.restrict E))
    (hDu : ∀ i j E, IsCompact E → MemLp (Du i j) 2 (volume.restrict E))
    (hw : ∀ i j, HasLocalWeakCoordinateDerivative (u i) (Du i j) j)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∫ x, rawWeakSourceVectorAdjoint d.potential u Du x * ψ x ∂potentialMeasure d.potential) =
      ∑ i : Fin n, ∫ x, u i x * coordinateDerivative ψ i x ∂potentialMeasure d.potential := by
  have hφuLoc (i : Fin n) : LocallyIntegrable
      (fun x => coordinateDerivative d.potential i x * u i x) volume :=
    locallyIntegrable_of_memLp_two_on_compacts fun E hE =>
      (memLp_continuous_top_on_compact
        (contDiff_coordinateDerivative d.source_C1 (m := 0) (by norm_num) i).continuous hE).mul
          (hu i E hE)
  have hDuψ (i : Fin n) : Integrable (fun x => Du i i x * ψ x) (potentialMeasure d.potential) :=
    integrable_raw_mul_compact_potential d.source_C1.continuous
      (locallyIntegrable_of_memLp_two_on_compacts (hDu i i)) hψ.continuous hc
  have hφuψ (i : Fin n) : Integrable
      (fun x => (coordinateDerivative d.potential i x * u i x) * ψ x)
      (potentialMeasure d.potential) :=
    integrable_raw_mul_compact_potential d.source_C1.continuous (hφuLoc i) hψ.continuous hc
  have huDψ (i : Fin n) : Integrable (fun x => u i x * coordinateDerivative ψ i x)
      (potentialMeasure d.potential) :=
    integrable_raw_mul_compact_potential d.source_C1.continuous
      (locallyIntegrable_of_memLp_two_on_compacts (hu i))
      (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous
      (hasCompactSupport_coordinateDerivative hc i)
  have hDψu (i : Fin n) : Integrable (fun x => coordinateDerivative ψ i x * u i x)
      (potentialMeasure d.potential) :=
    (huDψ i).congr (Eventually.of_forall fun x => mul_comm _ _)
  have hδψ (i : Fin n) : Integrable
      (fun x => rawWeakSourceAdjoint d.potential (u i) (Du i i) i x * ψ x)
      (potentialMeasure d.potential) := by
    apply ((hφuψ i).sub (hDuψ i)).congr
    exact Eventually.of_forall fun x => by dsimp only [rawWeakSourceAdjoint, Pi.sub_apply]; ring
  have hi (i : Fin n) :
      (∫ x, rawWeakSourceAdjoint d.potential (u i) (Du i i) i x * ψ x
        ∂potentialMeasure d.potential) =
      ∫ x, u i x * coordinateDerivative ψ i x ∂potentialMeasure d.potential := by
    have he := compact_source_adjoint_pair_weak d.source_C1 hψ hc (hw i i)
    have hleft :
        (∫ x, coordinateSourceAdjoint d.potential ψ i x * u i x ∂potentialMeasure d.potential) =
        (∫ x, (coordinateDerivative d.potential i x * u i x) * ψ x ∂potentialMeasure d.potential) -
          ∫ x, coordinateDerivative ψ i x * u i x ∂potentialMeasure d.potential := by
      rw [← integral_sub (hφuψ i) (hDψu i)]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only [coordinateSourceAdjoint]; ring
    have hright : (∫ x, ψ x * Du i i x ∂potentialMeasure d.potential) =
        ∫ x, Du i i x * ψ x ∂potentialMeasure d.potential :=
      integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
    have hδ :
        (∫ x, rawWeakSourceAdjoint d.potential (u i) (Du i i) i x * ψ x ∂potentialMeasure d.potential) =
        (∫ x, (coordinateDerivative d.potential i x * u i x) * ψ x ∂potentialMeasure d.potential) -
          ∫ x, Du i i x * ψ x ∂potentialMeasure d.potential := by
      rw [← integral_sub (hφuψ i) (hDuψ i)]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only [rawWeakSourceAdjoint, Pi.sub_apply]; ring
    have hcomm : (∫ x, coordinateDerivative ψ i x * u i x ∂potentialMeasure d.potential) =
        ∫ x, u i x * coordinateDerivative ψ i x ∂potentialMeasure d.potential :=
      integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
    rw [hleft, hright] at he
    rw [hδ, ← hcomm]
    linarith
  simp only [rawWeakSourceVectorAdjoint, Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (fun i _ => hδψ i)]
  exact Finset.sum_congr rfl fun i _ => hi i

theorem raw_vector_source_adjoint_eq_of_compact_divergence (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (u : Fin n → Space n → ℝ) (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (u i) 2 (volume.restrict E))
    (hDu : ∀ i j E, IsCompact E → MemLp (Du i j) 2 (volume.restrict E))
    (hw : ∀ i j, HasLocalWeakCoordinateDerivative (u i) (Du i j) j)
    (hdiv : ∀ ψ : Space n → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∑ i : Fin n, ∫ x, u i x * coordinateDerivative ψ i x ∂potentialMeasure d.potential) =
        ∫ x, g x * ψ x ∂potentialMeasure d.potential) :
    rawWeakSourceVectorAdjoint d.potential u Du =ᵐ[potentialMeasure d.potential] (g : Space n → ℝ) := by
  let δu := rawWeakSourceVectorAdjoint d.potential u Du
  have hδE (E : Set (Space n)) (hE : IsCompact E) : MemLp δu 2 (volume.restrict E) := by
    apply memLp_finsetSum Finset.univ
    intro i _
    have hφi := memLp_continuous_top_on_compact
      (contDiff_coordinateDerivative d.source_C1 (m := 0) (by norm_num) i).continuous hE
    exact (hφi.mul (hu i E hE)).sub (hDu i i E hE)
  have hρδE (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => Real.exp (-d.potential x) * δu x) 2 (volume.restrict E) :=
    memLp_continuous_mul_on_compact hE (hδE E hE)
      (Real.continuous_exp.comp d.source_C1.continuous.neg)
  have he : (fun x => Real.exp (-d.potential x) * δu x) =ᵐ[volume]
      (fun x => Real.exp (-d.potential x) * g x) := by
    apply ae_eq_of_integral_contDiff_smul_eq
      (locallyIntegrable_of_memLp_two_on_compacts hρδE)
      (locallyIntegrable_of_memLp_two_on_compacts fun E hE => regularizedDensityForcing_local_L2 d g hE)
    intro ψ hψ hc
    have hp := raw_vector_source_adjoint_local_compact_pair d u Du hu hDu hw
      (hψ.of_le (by simp)) hc
    have ht := hp.trans (hdiv ψ (hψ.of_le (by simp)) hc)
    simp_rw [integral_potentialMeasure d.source_C1.continuous.measurable] at ht
    simpa only [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using ht
  have hvol : δu =ᵐ[volume] (g : Space n → ℝ) := by
    filter_upwards [he] with x hx
    exact mul_left_cancel₀ (Real.exp_ne_zero _) hx
  exact (withDensity_absolutelyContinuous _ _).ae_eq hvol

theorem naturalCanonicalFlux_adjoint_eq_forcing_ae (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i j E, IsCompact E → MemLp (Du i j) 2 (volume.restrict E))
    (hw : ∀ i j, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i j) j) :
    rawWeakSourceVectorAdjoint d.potential (naturalCanonicalFlux d g) Du =ᵐ[potentialMeasure d.potential]
      (g : Space n → ℝ) := by
  obtain ⟨D, _, _, _, _, _, _, _, hdiv⟩ := exists_naturalCanonicalFlux_gaffney d hn g hg
  exact raw_vector_source_adjoint_eq_of_compact_divergence d g _ Du hu hDu hw hdiv

theorem quadratic_flux_jacobian_adjoint_eq_forcing_ae (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (B : Matrix (Fin n) (Fin n) ℝ) :
    rawWeakSourceVectorAdjoint d.potential (naturalCanonicalFlux d (quadraticSourceDatum d B))
      (quadraticFluxJacobian d hn hμ B) =ᵐ[potentialMeasure d.potential]
        (quadraticSourceDatum d B : Space n → ℝ) :=
  naturalCanonicalFlux_adjoint_eq_forcing_ae d hn (quadraticSourceDatum d B)
    (quadraticSourceDatum_mean_zero d hμ B) _
    (fun a _ hE => quadratic_row_flux_local_L2 d hn hμ B a hE)
    (fun a b _ hE => quadratic_flux_jacobian_local_L2 d hn hμ B a b hE)
    (quadratic_flux_jacobian_weak d hn hμ B)

end KLSConstantImprovement.ActualNaturalFluxAdjoint405

#print axioms KLSConstantImprovement.ActualNaturalFluxAdjoint405.raw_vector_source_adjoint_local_compact_pair
#print axioms KLSConstantImprovement.ActualNaturalFluxAdjoint405.naturalCanonicalFlux_adjoint_eq_forcing_ae
#print axioms KLSConstantImprovement.ActualNaturalFluxAdjoint405.quadratic_flux_jacobian_adjoint_eq_forcing_ae

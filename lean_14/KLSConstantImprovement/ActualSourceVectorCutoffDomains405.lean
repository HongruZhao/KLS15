import KLSConstantImprovement.ActualSourceRegularizedFluxDivergence405
import KLSConstantImprovement.ActualBoundedRawMetricDomain
import KLS.LocalWeakDerivativeCutoff

/-!
Actual compact H1 domains for vector cutoffs. Only local L2 control of
the raw Jacobian is needed. The compact derivative has its exact product
formula, compact support, and proved global source L2 membership. These
are precisely the domains of the accepted compact source-vector Bochner
identity, before any global Jacobian integrability is obtained.
-/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceVectorCutoffDomains405
open KLS ActualBoundedCanonicalSource ActualBoundedRawMetricDomain
open ActualCompactWeakSourceVectorBochner ActualCompactWeakSourceVectorSquare
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

def sourceVectorCutoffDerivative (χ : Space n → ℝ)
    (u : Fin n → Space n → ℝ) (Du : Fin n → Fin n → Space n → ℝ)
    (i j : Fin n) (x : Space n) : ℝ :=
  χ x * Du i j x + coordinateDerivative χ j x * u i x

theorem source_vector_compact_cutoff_domains (d : SourceData μ)
    (u : Fin n → Space n → ℝ) (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i, MemLp (u i) 2 (potentialMeasure d.potential))
    (hDu : ∀ i j E, IsCompact E → MemLp (Du i j) 2 (volume.restrict E))
    (hw : ∀ i j, HasLocalWeakCoordinateDerivative (u i) (Du i j) j)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) :
    ∀ i : Fin n, HasCompactSupport (fun x => χ x * u i x) ∧
      MemLp (fun x => χ x * u i x) 2 (potentialMeasure d.potential) ∧
      ∀ j : Fin n, HasCompactSupport (sourceVectorCutoffDerivative χ u Du i j) ∧
        MemLp (sourceVectorCutoffDerivative χ u Du i j) 2 (potentialMeasure d.potential) ∧
        HasLocalWeakCoordinateDerivative (fun x => χ x * u i x)
          (sourceVectorCutoffDerivative χ u Du i j) j := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hχtop : MemLp χ ∞ (potentialMeasure d.potential) := hχ.continuous.memLp_of_hasCompactSupport hc
  have huV (i : Fin n) (E : Set (Space n)) (hE : IsCompact E) : MemLp (u i) 2 (volume.restrict E) :=
    KLS.MemLp.restrict_volume_of_potentialMeasure (hu i) d.source_C1.continuous hE
  intro i
  refine ⟨hc.mul_right, hχtop.mul (hu i), ?_⟩
  intro j
  have hDχtop : MemLp (coordinateDerivative χ j) ∞ (potentialMeasure d.potential) :=
    (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) j).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_coordinateDerivative hc j)
  have hχDuV : MemLp (fun x => χ x * Du i j x) 2 volume :=
    memLp_compact_mul_of_local hχ.continuous hc (hDu i j)
  have hχDu : MemLp (fun x => χ x * Du i j x) 2 (potentialMeasure d.potential) :=
    memLp_potentialMeasure_of_compact_localL2 d.source_C1.continuous hc.mul_right
      (fun E _ => hχDuV.restrict E)
  refine ⟨hc.mul_right.add (hasCompactSupport_coordinateDerivative hc j).mul_right,
    hχDu.add (hDχtop.mul (hu i)), ?_⟩
  obtain ⟨W, hW, hWe⟩ := (hw i j).compact_mul (huV i) (hDu i j) hχ hc
  have hW' : HasLocalWeakCoordinateDerivative (fun x => χ x * u i x) (fun x => W x) j := by
    intro ψ hψ hψc
    exact hW ψ hψ hψc
  apply hW'.congr_ae EventuallyEq.rfl
  filter_upwards [hWe] with x hx
  change W x = χ x * Du i j x + coordinateDerivative χ j x * u i x
  exact hx

theorem rawWeakSourceVectorAdjoint_cutoff (φ χ : Space n → ℝ)
    (u : Fin n → Space n → ℝ) (Du : Fin n → Fin n → Space n → ℝ) (x : Space n) :
    rawWeakSourceVectorAdjoint φ (fun i y => χ y * u i y) (sourceVectorCutoffDerivative χ u Du) x =
      χ x * rawWeakSourceVectorAdjoint φ u Du x - ∑ i : Fin n, coordinateDerivative χ i x * u i x := by
  simp only [rawWeakSourceVectorAdjoint, rawWeakSourceAdjoint, sourceVectorCutoffDerivative,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem integral_source_vector_compact_cutoff_bochner (d : SourceData μ)
    (u : Fin n → Space n → ℝ) (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i, MemLp (u i) 2 (potentialMeasure d.potential))
    (hDu : ∀ i j E, IsCompact E → MemLp (Du i j) 2 (volume.restrict E))
    (hw : ∀ i j, HasLocalWeakCoordinateDerivative (u i) (Du i j) j)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) :
    (∫ x, (χ x * rawWeakSourceVectorAdjoint d.potential u Du x -
      ∑ i : Fin n, coordinateDerivative χ i x * u i x)^2 ∂potentialMeasure d.potential) =
      ∫ x, ∑ i : Fin n, ∑ j : Fin n,
        (coordinateHessian d.potential x i j * (χ x * u i x) * (χ x * u j x) +
          sourceVectorCutoffDerivative χ u Du i j x * sourceVectorCutoffDerivative χ u Du j i x)
            ∂potentialMeasure d.potential := by
  have hd := source_vector_compact_cutoff_domains d u Du hu hDu hw hχ hc
  have he := integral_compact_rawWeak_source_vector_adjoint_square d.source_C1 d.source_lipschitz
    d.gradient_lipschitz (fun i x => χ x * u i x) (sourceVectorCutoffDerivative χ u Du)
    (fun i => (hd i).1) (fun i => (hd i).2.1)
    (fun i j => ((hd i).2.2 j).2.1) (fun i j => ((hd i).2.2 j).1)
    (fun i j => ((hd i).2.2 j).2.2)
  simpa only [rawWeakSourceVectorAdjoint_cutoff] using he

end KLSConstantImprovement.ActualSourceVectorCutoffDomains405
#print axioms KLSConstantImprovement.ActualSourceVectorCutoffDomains405.source_vector_compact_cutoff_domains
#print axioms KLSConstantImprovement.ActualSourceVectorCutoffDomains405.rawWeakSourceVectorAdjoint_cutoff
#print axioms KLSConstantImprovement.ActualSourceVectorCutoffDomains405.integral_source_vector_compact_cutoff_bochner

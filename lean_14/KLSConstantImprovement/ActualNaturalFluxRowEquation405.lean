import KLSConstantImprovement.ActualLocalDivergenceTests405

/-! The actual differentiated natural Poisson equation.  It is derived
from the constructed inverse and genuine weak derivatives, using the
compact source adjoint as an admissible locally Lipschitz test.  No
second derivative of the source or extra row PDE is assumed. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualNaturalFluxRowEquation405
open KLS ActualBoundedCanonicalSource ActualSourceNaturalGaffney405
open ActualLocalDivergenceTests405 ActualWeakSourceCompactVectorBochner
open ActualCompactSourceVectorBochner
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {n : ℕ} {μ : Measure (Space n)}

theorem natural_flux_differentiated_compact_equation (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i j E, IsCompact E → MemLp (Du i j) 2 (volume.restrict E))
    (hw : ∀ i j, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i j) j)
    {Dg : Space n → ℝ} {j : Fin n}
    (hgw : HasLocalWeakCoordinateDerivative (g : Space n → ℝ) Dg j)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) :
    (∑ i : Fin n, ∫ x, Du i j x * coordinateDerivative ψ i x ∂potentialMeasure d.potential) +
      (∑ i : Fin n, ∫ x, coordinateHessian d.potential x i j * naturalCanonicalFlux d g i x * ψ x
        ∂potentialMeasure d.potential) =
      ∫ x, Dg x * ψ x ∂potentialMeasure d.potential := by
  let u := naturalCanonicalFlux d g
  let a := coordinateSourceAdjoint d.potential ψ j
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hal : LocallyLipschitz a := locallyLipschitz_sourceAdjoint
    d.gradient_lipschitz.locallyLipschitz hψ j
  have hacomp : HasCompactSupport a := by
    exact hc.mul_left.sub (hasCompactSupport_coordinateDerivative hc j)
  have hv := naturalCanonicalFlux_locallyLipschitz_test d hn g hg hal hacomp
  have hgp := compact_source_adjoint_pair_weak d.source_C1 hψ1 hc hgw
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) :=
    withDensity_absolutelyContinuous _ _
  have hderiv (i : Fin n) :
      coordinateDerivative a i =ᵐ[potentialMeasure d.potential] fun x =>
        coordinateHessian d.potential x i j * ψ x +
          coordinateSourceAdjoint d.potential (coordinateDerivative ψ i) j x := by
    have hd := locallyLipschitz_ae_differentiableAt (μ := volume)
      (locallyLipschitz_coordinateDerivative_of_gradient d.gradient_lipschitz.locallyLipschitz j)
    filter_upwards [hd.filter_mono hac.ae_le] with x hx
    have he := coordinateDerivative_sourceAdjoint_at i j hx hψ
    have hs := (coordinateHessian_symmetric hψ x).apply i j
    change coordinateHessian ψ x j i = coordinateHessian ψ x i j at hs
    change coordinateDerivative (coordinateSourceAdjoint d.potential ψ j) i x = _
    rw [he]
    dsimp only [coordinateSourceAdjoint]
    change _ = coordinateHessian d.potential x i j * ψ x +
      (coordinateDerivative d.potential j x * coordinateDerivative ψ i x - coordinateHessian ψ x j i)
    rw [hs]
    ring
  have hHi (i : Fin n) : LocallyIntegrable
      (fun x => coordinateHessian d.potential x i j * u i x) volume :=
    locallyIntegrable_of_memLp_two_on_compacts fun E hE =>
      (KLS.MemLp.restrict_volume_of_potentialMeasure (d.hessian_entry_memLp i j ∞)
        d.source_C1.continuous hE).mul (hu i E hE)
  have hi (i : Fin n) :
      (∫ x, u i x * coordinateDerivative a i x ∂potentialMeasure d.potential) =
        (∫ x, coordinateHessian d.potential x i j * u i x * ψ x ∂potentialMeasure d.potential) +
        ∫ x, Du i j x * coordinateDerivative ψ i x ∂potentialMeasure d.potential := by
    have hDiψ : ContDiff ℝ 1 (coordinateDerivative ψ i) :=
      contDiff_coordinateDerivative hψ (by norm_num) i
    have hDci := hasCompactSupport_coordinateDerivative hc i
    have hcontAdj : Continuous (coordinateSourceAdjoint d.potential (coordinateDerivative ψ i) j) :=
      ((contDiff_coordinateDerivative d.source_C1 (m := 0) (by norm_num) j).continuous.mul
        hDiψ.continuous).sub
          (contDiff_coordinateDerivative hDiψ (m := 0) (by norm_num) j).continuous
    have hcompAdj : HasCompactSupport
        (coordinateSourceAdjoint d.potential (coordinateDerivative ψ i) j) :=
      hDci.mul_left.sub (hasCompactSupport_coordinateDerivative hDci j)
    have hcurv : Integrable
        (fun x => coordinateHessian d.potential x i j * u i x * ψ x)
        (potentialMeasure d.potential) :=
      integrable_raw_mul_compact_potential d.source_C1.continuous (hHi i) hψ.continuous hc
    have hrem : Integrable (fun x => u i x *
        coordinateSourceAdjoint d.potential (coordinateDerivative ψ i) j x)
        (potentialMeasure d.potential) :=
      integrable_raw_mul_compact_potential d.source_C1.continuous
        (locallyIntegrable_of_memLp_two_on_compacts (hu i)) hcontAdj hcompAdj
    have hpart := compact_source_adjoint_pair_weak d.source_C1 hDiψ hDci (hw i j)
    calc
      _ = ∫ x, (coordinateHessian d.potential x i j * u i x * ψ x +
          u i x * coordinateSourceAdjoint d.potential (coordinateDerivative ψ i) j x)
          ∂potentialMeasure d.potential := by
        apply integral_congr_ae
        filter_upwards [hderiv i] with x hx
        rw [hx]
        ring
      _ = (∫ x, coordinateHessian d.potential x i j * u i x * ψ x ∂potentialMeasure d.potential) +
          ∫ x, u i x * coordinateSourceAdjoint d.potential (coordinateDerivative ψ i) j x
            ∂potentialMeasure d.potential := integral_add hcurv hrem
      _ = _ := by
        congr 1
        calc
          _ = ∫ x, coordinateSourceAdjoint d.potential (coordinateDerivative ψ i) j x * u i x
              ∂potentialMeasure d.potential := integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
          _ = ∫ x, coordinateDerivative ψ i x * Du i j x ∂potentialMeasure d.potential := hpart
          _ = _ := integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
  have hsum : (∑ i : Fin n, ∫ x, u i x * coordinateDerivative a i x ∂potentialMeasure d.potential) =
      (∑ i : Fin n, ∫ x, coordinateHessian d.potential x i j * u i x * ψ x
        ∂potentialMeasure d.potential) +
      (∑ i : Fin n, ∫ x, Du i j x * coordinateDerivative ψ i x ∂potentialMeasure d.potential) := by
    simp_rw [hi, Finset.sum_add_distrib]
  have hgpair : (∫ x, g x * a x ∂potentialMeasure d.potential) =
      ∫ x, Dg x * ψ x ∂potentialMeasure d.potential := by
    calc
      _ = ∫ x, coordinateSourceAdjoint d.potential ψ j x * g x ∂potentialMeasure d.potential :=
        integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
      _ = ∫ x, ψ x * Dg x ∂potentialMeasure d.potential := hgp
      _ = _ := integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
  change (∑ i, ∫ x, u i x * coordinateDerivative a i x ∂potentialMeasure d.potential) = _ at hv
  rw [hsum, hgpair] at hv
  linarith

end KLSConstantImprovement.ActualNaturalFluxRowEquation405

#print axioms KLSConstantImprovement.ActualNaturalFluxRowEquation405.natural_flux_differentiated_compact_equation

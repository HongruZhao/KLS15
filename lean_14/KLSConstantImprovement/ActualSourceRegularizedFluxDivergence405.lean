import KLSConstantImprovement.ActualSourceRegularizedFluxCompatibility405
import KLSConstantImprovement.ActualCompactWeakSourceVectorSquare
import KLSConstantImprovement.ActualWeakSourceCompactVectorBochner
import KLS.WeakBochner

/-!
The actual regularized flux has source adjoint equal to the actual L2
forcing. Its Jacobian is only locally L2 at this stage; that is sufficient
for compact weighted integration by parts and distribution uniqueness.
No global Jacobian integrability is assumed before the Gaffney estimate.
-/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceRegularizedFluxDivergence405
open KLS ActualBoundedCanonicalSource ActualSourceMetricRegularization405
open ActualSourceInverseMetricRegularization405 ActualSourceRegularizedEnergyForm405
open ActualSourceRegularizedLocalEquation405 ActualSourceRegularizedFluxH1405
open ActualSourceRegularizedFluxCompatibility405
open ActualCompactWeakSourceVectorBochner ActualCompactWeakSourceVectorSquare
open ActualWeakSourceCompactVectorBochner ActualCompactSourceVectorBochner
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

/-- Weighted adjoint pairing needs only genuine local weak derivatives
and compact tests; the vector derivative need not be globally L2. -/
theorem raw_vector_source_adjoint_compact_pair (d : SourceData μ)
    (u : Fin n → Space n → ℝ) (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i, MemLp (u i) 2 (potentialMeasure d.potential))
    (hDu : ∀ i j E, IsCompact E → MemLp (Du i j) 2 (volume.restrict E))
    (hw : ∀ i j, HasLocalWeakCoordinateDerivative (u i) (Du i j) j)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∫ x, rawWeakSourceVectorAdjoint d.potential u Du x * ψ x ∂potentialMeasure d.potential) =
      ∑ i : Fin n, ∫ x, u i x * coordinateDerivative ψ i x ∂potentialMeasure d.potential := by
  have hψ2 := memLp_of_continuous_hasCompactSupport d.source_C1.continuous hψ.continuous hc
  have hφu (i : Fin n) : MemLp (fun x => coordinateDerivative d.potential i x * u i x)
      2 (potentialMeasure d.potential) :=
    (source_coordinate_memLp_top_of_lipschitz d.source_lipschitz (potentialMeasure d.potential) i).mul (hu i)
  have hDuψ (i : Fin n) : Integrable (fun x => Du i i x * ψ x) (potentialMeasure d.potential) :=
    integrable_raw_mul_compact_potential d.source_C1.continuous
      (locallyIntegrable_of_memLp_two_on_compacts (hDu i i)) hψ.continuous hc
  have hφuψ (i : Fin n) : Integrable (fun x => (coordinateDerivative d.potential i x * u i x) * ψ x)
      (potentialMeasure d.potential) := (hφu i).integrable_mul hψ2
  have hDψu (i : Fin n) : Integrable (fun x => coordinateDerivative ψ i x * u i x)
      (potentialMeasure d.potential) :=
    (memLp_of_continuous_hasCompactSupport d.source_C1.continuous
      (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous
      (hasCompactSupport_coordinateDerivative hc i)).integrable_mul (hu i)
  have hδψ (i : Fin n) : Integrable (fun x => rawWeakSourceAdjoint d.potential (u i) (Du i i) i x * ψ x)
      (potentialMeasure d.potential) := by
    have hi := (hφuψ i).sub (hDuψ i)
    apply hi.congr
    exact Eventually.of_forall fun x => by dsimp only [rawWeakSourceAdjoint, Pi.sub_apply]; ring
  have hi (i : Fin n) : (∫ x, rawWeakSourceAdjoint d.potential (u i) (Du i i) i x * ψ x
      ∂potentialMeasure d.potential) =
      ∫ x, u i x * coordinateDerivative ψ i x ∂potentialMeasure d.potential := by
    have he := compact_source_adjoint_pair_weak d.source_C1 hψ hc (hw i i)
    have hleft : (∫ x, coordinateSourceAdjoint d.potential ψ i x * u i x ∂potentialMeasure d.potential) =
        (∫ x, (coordinateDerivative d.potential i x * u i x) * ψ x ∂potentialMeasure d.potential) -
          ∫ x, coordinateDerivative ψ i x * u i x ∂potentialMeasure d.potential := by
      rw [← integral_sub (hφuψ i) (hDψu i)]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only [coordinateSourceAdjoint]; ring
    have hright : (∫ x, ψ x * Du i i x ∂potentialMeasure d.potential) =
        ∫ x, Du i i x * ψ x ∂potentialMeasure d.potential :=
      integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
    have hδ : (∫ x, rawWeakSourceAdjoint d.potential (u i) (Du i i) i x * ψ x
        ∂potentialMeasure d.potential) =
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

theorem regularizedWeakFlux_compact_divergence_test (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    (∑ j : Fin n, ∫ x, regularizedWeakFlux d hn k hε g j x * coordinateDerivative ψ j x
      ∂potentialMeasure d.potential) = ∫ x, g x * ψ x ∂potentialMeasure d.potential := by
  let U := regularizedOrdinaryInverse d hn k hε g
  have hDψ (j : Fin n) : MemLp (coordinateDerivative ψ j) 2 (potentialMeasure d.potential) :=
    memLp_of_continuous_hasCompactSupport d.source_C1.continuous
      (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) j).continuous
      (hasCompactSupport_coordinateDerivative hc j)
  have hi (i j : Fin n) : Integrable (fun x => regularizedMetricInverse d k ε x j i *
      weightedH1Derivative d.potential i U x * coordinateDerivative ψ j x) (potentialMeasure d.potential) := by
    have hp : MemLp (fun x => regularizedMetricInverse d k ε x j i *
        weightedH1Derivative d.potential i U x) 2 (potentialMeasure d.potential) :=
      (regularizedMetricInverse_entry_memLp_top d k hε j i (potentialMeasure d.potential)).mul (Lp.memLp _)
    exact hp.integrable_mul (hDψ j)
  have hl : (∑ j : Fin n, ∫ x, regularizedWeakFlux d hn k hε g j x * coordinateDerivative ψ j x
      ∂potentialMeasure d.potential) =
      ∑ i : Fin n, ∑ j : Fin n, ∫ x, regularizedMetricInverse d k ε x i j *
        weightedH1Derivative d.potential i U x * coordinateDerivative ψ j x ∂potentialMeasure d.potential := by
    have hj (j : Fin n) : (∫ x, regularizedWeakFlux d hn k hε g j x * coordinateDerivative ψ j x
        ∂potentialMeasure d.potential) =
        ∑ i : Fin n, ∫ x, regularizedMetricInverse d k ε x j i *
          weightedH1Derivative d.potential i U x * coordinateDerivative ψ j x ∂potentialMeasure d.potential := by
      calc
        _ = ∫ x, ∑ i : Fin n, regularizedMetricInverse d k ε x j i *
            weightedH1Derivative d.potential i U x * coordinateDerivative ψ j x ∂potentialMeasure d.potential := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by
            change (∑ i : Fin n, regularizedMetricInverse d k ε x j i *
              weightedH1Derivative d.potential i U x) * coordinateDerivative ψ j x = _
            rw [Finset.sum_mul]
        _ = _ := integral_finsetSum Finset.univ (fun i _ => hi i j)
    rw [Finset.sum_congr rfl (fun j _ => hj j), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      have hs := (Matrix.isHermitian_iff_isSymm.mp
        (regularizedMetricInverse_posDef d k hε x).isHermitian).apply i j
      dsimp only
      rw [show regularizedMetricInverse d k ε x j i = regularizedMetricInverse d k ε x i j from hs]
  rw [hl]
  exact regularizedOrdinaryInverse_compact_test_mean_zero d hn k hε g hg hψ hc

theorem regularizedWeakFlux_adjoint_eq_forcing_ae (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0)
    (D : Fin n → Fin n → Space n → ℝ)
    (hD : ∀ i j E, IsCompact E → MemLp (D i j) 2 (volume.restrict E))
    (hw : ∀ i j, HasLocalWeakCoordinateDerivative
      (weightedH1Derivative d.potential i (regularizedOrdinaryInverse d hn k hε g)) (D i j) j) :
    rawWeakSourceVectorAdjoint d.potential (regularizedWeakFlux d hn k hε g)
      (regularizedFluxDerivative d hn k hε g D) =ᵐ[potentialMeasure d.potential] (g : Space n → ℝ) := by
  let u := regularizedWeakFlux d hn k hε g
  let Du := regularizedFluxDerivative d hn k hε g D
  let δu := rawWeakSourceVectorAdjoint d.potential u Du
  have hu (i : Fin n) : MemLp (u i) 2 (potentialMeasure d.potential) := regularizedWeakFlux_memLp d hn k hε g i
  have huE (i : Fin n) (E : Set (Space n)) (hE : IsCompact E) : MemLp (u i) 2 (volume.restrict E) :=
    KLS.MemLp.restrict_volume_of_potentialMeasure (hu i) d.source_C1.continuous hE
  have hDu (i j : Fin n) (E : Set (Space n)) (hE : IsCompact E) : MemLp (Du i j) 2 (volume.restrict E) :=
    regularizedFluxDerivative_local_L2 d hn k hε g D hD i j hE
  have hDuw (i j : Fin n) : HasLocalWeakCoordinateDerivative (u i) (Du i j) j :=
    regularizedWeakFlux_hasLocalWeakDerivative d hn k hε g D hD hw i j
  have hδE (E : Set (Space n)) (hE : IsCompact E) : MemLp δu 2 (volume.restrict E) := by
    apply memLp_finsetSum Finset.univ
    intro i _
    have hφi := memLp_continuous_top_on_compact
      (contDiff_coordinateDerivative d.source_C1 (m := 0) (by norm_num) i).continuous hE
    exact (hφi.mul (huE i E hE)).sub (hDu i i E hE)
  have hρδE (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => Real.exp (-d.potential x) * δu x) 2 (volume.restrict E) :=
    memLp_continuous_mul_on_compact hE (hδE E hE)
      (Real.continuous_exp.comp d.source_C1.continuous.neg)
  have he : (fun x => Real.exp (-d.potential x) * δu x) =ᵐ[volume]
      (fun x => Real.exp (-d.potential x) * g x) := by
    apply ae_eq_of_integral_contDiff_smul_eq
      (locallyIntegrable_of_memLp_two_on_compacts hρδE)
      (locallyIntegrable_of_memLp_two_on_compacts (fun E hE => regularizedDensityForcing_local_L2 d g hE))
    intro ψ hψ hc
    have hp := raw_vector_source_adjoint_compact_pair d u Du hu hDu hDuw
      (hψ.of_le (by simp)) hc
    have hq := regularizedWeakFlux_compact_divergence_test d hn k hε g hg (hψ.of_le (by simp)) hc
    have ht := hp.trans hq
    simp_rw [integral_potentialMeasure d.source_C1.continuous.measurable] at ht
    simpa only [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using ht
  have hvol : δu =ᵐ[volume] (g : Space n → ℝ) := by
    filter_upwards [he] with x hx
    exact mul_left_cancel₀ (Real.exp_ne_zero _) hx
  exact (withDensity_absolutelyContinuous _ _).ae_eq hvol

end KLSConstantImprovement.ActualSourceRegularizedFluxDivergence405
#print axioms KLSConstantImprovement.ActualSourceRegularizedFluxDivergence405.raw_vector_source_adjoint_compact_pair
#print axioms KLSConstantImprovement.ActualSourceRegularizedFluxDivergence405.regularizedWeakFlux_compact_divergence_test
#print axioms KLSConstantImprovement.ActualSourceRegularizedFluxDivergence405.regularizedWeakFlux_adjoint_eq_forcing_ae

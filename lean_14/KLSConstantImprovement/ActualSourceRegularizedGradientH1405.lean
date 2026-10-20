import KLSConstantImprovement.ActualSourceRegularizedGradientLocalH1405
import KLS.LocalWeakProduct
import KLS.LocalWeakAlgebra

/-!
A single genuine raw local-L2 Hessian for the constructed regularized
inverse. Compact C1 localization of the proved interior weak derivatives
supplies the ordinary cut-off graph; retained distribution uniqueness
glues these derivatives on the whole space. Mixed derivatives commute by
two weak integrations by parts. No strong operator core is used.
-/
noncomputable section
open MeasureTheory Set Filter Matrix Metric InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceRegularizedGradientH1405
open KLS ActualBoundedCanonicalSource ActualSourceRegularizedEnergyForm405
open ActualSourceRegularizedGradientLocalH1405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

/-- A compact C1 multiplier supported inside an actual local weak test
domain gives a genuine global L2 weak derivative, with its exact formula. -/
theorem compact_mul_weakDerivative_of_local_C1_tests
    {p χ : Space n → ℝ} {B : Set (Space n)} {j : Fin n}
    (hp : ∀ E : Set (Space n), IsCompact E → MemLp p 2 (volume.restrict E))
    (F : Lp ℝ 2 (volume : Measure (Space n)))
    (hw : ∀ ψ : Space n → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ B →
      (∫ x, p x * coordinateDerivative ψ j x) = -(∫ x, F x * ψ x))
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) (hχB : tsupport χ ⊆ B) :
    ∃ W : Lp ℝ 2 (volume : Measure (Space n)),
      HasWeakCoordinateDerivative (fun x => χ x * p x) j W ∧
      (W : Space n → ℝ) =ᵐ[volume] fun x => χ x * F x + coordinateDerivative χ j x * p x := by
  have hcp := memLp_compact_mul_of_local hχ.continuous hc hp
  have hcF := memLp_compact_mul_of_local hχ.continuous hc
    (fun E _ => (Lp.memLp F).restrict E)
  have hdcp := memLp_compact_mul_of_local
    (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) j).continuous
    (hasCompactSupport_coordinateDerivative hc j) hp
  have hW : MemLp (fun x => χ x * F x + coordinateDerivative χ j x * p x) 2 volume := hcF.add hdcp
  let W : Lp ℝ 2 volume := hW.toLp (fun x => χ x * F x + coordinateDerivative χ j x * p x)
  refine ⟨W, ?_, hW.coeFn_toLp⟩
  intro ψ hψ hψc
  have hψ2 : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
  have hdψ2 : MemLp (coordinateDerivative ψ j) 2 volume :=
    (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) j).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_coordinateDerivative hψc j)
  have ha : Integrable (fun x => (χ x * F x) * ψ x) volume := hcF.integrable_mul hψ2
  have hb : Integrable (fun x => (coordinateDerivative χ j x * p x) * ψ x) volume :=
    hdcp.integrable_mul hψ2
  have hd : Integrable (fun x => (χ x * p x) * coordinateDerivative ψ j x) volume :=
    hcp.integrable_mul hdψ2
  have he := hw (fun x => χ x * ψ x) (hχ.mul hψ) hc.mul_right
    (tsupport_mul_subset_left.trans hχB)
  have hl : (∫ x, p x * coordinateDerivative (fun y => χ y * ψ y) j x) =
      (∫ x, (coordinateDerivative χ j x * p x) * ψ x) +
        ∫ x, (χ x * p x) * coordinateDerivative ψ j x := by
    rw [← integral_add hb hd]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [coordinateDerivative_mul (hχ.differentiable (by norm_num) x)
        (hψ.differentiable (by norm_num) x)]
      ring
  have hr : (∫ x, F x * (χ x * ψ x)) = ∫ x, (χ x * F x) * ψ x :=
    integral_congr_ae (Eventually.of_forall fun _ => by ring)
  have hWi : (∫ x, W x * ψ x) = (∫ x, (χ x * F x) * ψ x) +
      ∫ x, (coordinateDerivative χ j x * p x) * ψ x := by
    rw [← integral_add ha hb]
    apply integral_congr_ae
    filter_upwards [hW.coeFn_toLp] with x hx
    change W x * ψ x = _
    rw [show W x = χ x * F x + coordinateDerivative χ j x * p x from hx]
    ring
  rw [hl, hr] at he
  rw [hWi]
  linarith

theorem ordinary_graph_raw_hessian_symmetric (d : SourceData μ)
    (U : WeightedCenteredH1 d.potential) (D : Fin n → Fin n → Space n → ℝ)
    (hD : ∀ i j E, IsCompact E → MemLp (D i j) 2 (volume.restrict E))
    (hw : ∀ i j, HasLocalWeakCoordinateDerivative (weightedH1Derivative d.potential i U) (D i j) j)
    (i j : Fin n) : D i j =ᵐ[volume] D j i := by
  apply ae_eq_of_integral_contDiff_smul_eq
    (locallyIntegrable_of_memLp_two_on_compacts (hD i j))
    (locallyIntegrable_of_memLp_two_on_compacts (hD j i))
  intro ψ hψ hc
  have hi := hw i j ψ (hψ.of_le (by simp)) hc
  have hj := hw j i ψ (hψ.of_le (by simp)) hc
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by simp)
  have hψi : ContDiff ℝ 1 (coordinateDerivative ψ i) :=
    contDiff_coordinateDerivative hψ2 (m := 1) (by norm_num) i
  have hψj : ContDiff ℝ 1 (coordinateDerivative ψ j) :=
    contDiff_coordinateDerivative hψ2 (m := 1) (by norm_num) j
  have hui := weightedH1_unweighted_weak_identity d.source_C1 U hψj
    (hasCompactSupport_coordinateDerivative hc j) i
  have huj := weightedH1_unweighted_weak_identity d.source_C1 U hψi
    (hasCompactSupport_coordinateDerivative hc i) j
  have hsym : (∫ x, weightedH1Value d.potential U x * coordinateDerivative (coordinateDerivative ψ j) i x) =
      ∫ x, weightedH1Value d.potential U x * coordinateDerivative (coordinateDerivative ψ i) j x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      have hs := (coordinateHessian_symmetric hψ2 x).apply i j
      change coordinateHessian ψ x j i = coordinateHessian ψ x i j at hs
      change weightedH1Value d.potential U x * coordinateHessian ψ x i j =
        weightedH1Value d.potential U x * coordinateHessian ψ x j i
      rw [hs]
  have he : (∫ x, D i j x * ψ x) = ∫ x, D j i x * ψ x := by linarith
  simpa only [smul_eq_mul, mul_comm] using he

/-- The actual regularized inverse has one global raw weak Hessian,
locally square integrable and symmetric almost everywhere. -/
theorem exists_regularizedOrdinaryGradient_rawH1
    (d : SourceData μ) (hn : 1 ≤ n) (k : ℕ) {ε : ℝ} (hε : 0 < ε)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0) :
    ∃ D : Fin n → Fin n → Space n → ℝ,
      (∀ i j E, IsCompact E → MemLp (D i j) 2 (volume.restrict E)) ∧
      (∀ i j, HasLocalWeakCoordinateDerivative
        (weightedH1Derivative d.potential i (regularizedOrdinaryInverse d hn k hε g)) (D i j) j) ∧
      (∀ᵐ x ∂(volume : Measure (Space n)), ∀ i j, D i j x = D j i x) := by
  let U := regularizedOrdinaryInverse d hn k hε g
  have hp (i : Fin n) : ∀ E : Set (Space n), IsCompact E →
      MemLp (weightedH1Derivative d.potential i U) 2 (volume.restrict E) :=
    fun _ hE => weightedH1Derivative_memLp_restrict d.source_C1.continuous U i hE
  have hraw (i j : Fin n) : ∃ D : Space n → ℝ,
      (∀ E : Set (Space n), IsCompact E → MemLp D 2 (volume.restrict E)) ∧
      HasLocalWeakCoordinateDerivative (weightedH1Derivative d.potential i U) D j := by
    apply exists_local_weakCoordinateDerivative_of_cutoffs j
    intro N
    have hχ : ContDiff ℝ 1 (smoothCutoff n N) := smoothCutoff_contDiff N
    have hχc : HasCompactSupport (smoothCutoff n N) := smoothCutoff_hasCompactSupport N
    obtain ⟨R, _, hχR, D, hD⟩ := exists_regularizedOrdinaryGradient_local_rawH1 d hn k hε g hg hχc
    obtain ⟨W, hW, _⟩ := compact_mul_weakDerivative_of_local_C1_tests (hp i) (D i j)
      (hD i j) hχ hχc hχR
    exact ⟨W, hW⟩
  choose D hD hw using hraw
  refine ⟨D, hD, hw, ?_⟩
  exact ae_all_iff.mpr fun i => ae_all_iff.mpr fun j =>
    ordinary_graph_raw_hessian_symmetric d U D hD hw i j

end KLSConstantImprovement.ActualSourceRegularizedGradientH1405
#print axioms KLSConstantImprovement.ActualSourceRegularizedGradientH1405.compact_mul_weakDerivative_of_local_C1_tests
#print axioms KLSConstantImprovement.ActualSourceRegularizedGradientH1405.ordinary_graph_raw_hessian_symmetric
#print axioms KLSConstantImprovement.ActualSourceRegularizedGradientH1405.exists_regularizedOrdinaryGradient_rawH1

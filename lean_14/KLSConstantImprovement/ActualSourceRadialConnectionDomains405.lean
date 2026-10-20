import KLSConstantImprovement.ActualSourceRadialConnectionTest405
import KLSConstantImprovement.ActualSourceRadialConnectionBoundary405
import KLSConstantImprovement.ActualIntrinsicRatioBounds405
import KLSConstantImprovement.ActualConnectionContractions405
import KLS.WeakWeightedIntegration

/-! Every signed compact radial H-equation term is integrable before any
cancellation, with no bounded natural mass premise. Only fixed radial scale
is used here. The uniform local estimate and radial limit are separate. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal NNReal
namespace KLSConstantImprovement.ActualSourceRadialConnectionDomains405
open KLS ActualBoundedCanonicalSource ActualSourceConnectionFields405
open ActualSourceCompactConnectionDomains405 ActualSourceRadialConnectionTest405
open ActualSourceRadialConnectionBoundary405 ActualIntrinsicRatioBounds405
open ActualRadialMatrixCalculus405 ActualSourceCurvatureDomains405 ActualSourceHessianEvolution405
open ActualSourceBoundedMassCutoffs405 ActualConnectionContractions405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

def sourceRadialExtra (d : SourceData μ) (u : Fin n → Space n → ℝ)
    (Du : Fin n → Fin n → Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n,
    ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
      (u i x * u j x) * (∑ k : Fin n, u k x * Du k a x)

theorem sourceRadialExtra_contraction (d : SourceData μ)
    (u : Fin n → Space n → ℝ) (Du : Fin n → Fin n → Space n → ℝ) (x : Space n) :
    sourceRadialExtra d u Du x =
      ((Matrix.of fun i a => Du i a x).transpose *ᵥ (fun i => u i x)) ⬝ᵥ
        ((coordinateHessian d.potential x)⁻¹ *ᵥ (sourceThirdAlong d u x *ᵥ (fun i => u i x))) := by
  have he := connection_boundary_contraction (coordinateHessian d.potential x)⁻¹
    (sourceThirdMatrix d x) (fun i => u i x)
    ((Matrix.of fun i a => Du i a x).transpose *ᵥ (fun i => u i x))
  simpa only [sourceRadialExtra, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Matrix.of_apply, sourceThirdAlong, ActualCanonicalConnectionAlgebra405.thirdAlong, mul_comm] using he

theorem radial_natural_coordinate_memLp_top (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) {δ : ℝ} (hδ : 0 < δ) (i : Fin n) :
    MemLp (fun x => naturalCanonicalFlux d g i x /
      radialDenom δ (fun a => naturalCanonicalFlux d g a x)) ∞ (potentialMeasure d.potential) := by
  let u := naturalCanonicalFlux d g
  have hu (a : Fin n) := naturalCanonicalFlux_aestronglyMeasurable d g a
  have hden : AEStronglyMeasurable (fun x => radialDenom δ (fun a => u a x))
      (potentialMeasure d.potential) :=
    aestronglyMeasurable_const.add ((Finset.aestronglyMeasurable_fun_sum Finset.univ
      (fun a _ => (hu a).pow 2)).const_mul δ)
  apply memLp_top_of_bound ((hu i).aemeasurable.div hden.aemeasurable).aestronglyMeasurable
    (1 + δ⁻¹)
  exact Eventually.of_forall fun x => by
    change ‖u i x / radialDenom δ (fun a => u a x)‖ ≤ 1 + δ⁻¹
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (radialDenom_positive hδ.le _)]
    exact radial_coordinate_ratio_le hδ (fun a => u a x) le_rfl i

theorem radial_natural_triple_memLp_top (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) {δ : ℝ} (hδ : 0 < δ) (i j k : Fin n) :
    MemLp (fun x => (naturalCanonicalFlux d g i x * naturalCanonicalFlux d g j x *
      naturalCanonicalFlux d g k x) / radialDenom δ (fun a => naturalCanonicalFlux d g a x) ^ 2)
      ∞ (potentialMeasure d.potential) := by
  let u := naturalCanonicalFlux d g
  have hu (a : Fin n) := naturalCanonicalFlux_aestronglyMeasurable d g a
  have hden : AEStronglyMeasurable (fun x => radialDenom δ (fun a => u a x))
      (potentialMeasure d.potential) :=
    aestronglyMeasurable_const.add ((Finset.aestronglyMeasurable_fun_sum Finset.univ
      (fun a _ => (hu a).pow 2)).const_mul δ)
  apply memLp_top_of_bound ((((hu i).mul (hu j)).mul (hu k)).aemeasurable.div
    (hden.pow 2).aemeasurable).aestronglyMeasurable (δ⁻¹ * (1 + δ⁻¹))
  exact Eventually.of_forall fun x => by
    change ‖(u i x * u j x * u k x) / radialDenom δ (fun a => u a x) ^ 2‖ ≤ δ⁻¹ * (1 + δ⁻¹)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos (radialDenom_positive hδ.le _))]
    exact radial_triple_ratio_le hδ (fun a => u a x) le_rfl i j k

theorem actual_compact_radial_connection_fields_integrable (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) {δ : ℝ} (hδ : 0 < δ)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hDu : ∀ i a E, IsCompact E → MemLp (Du i a) 2 (volume.restrict E))
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) :
    Integrable (fun x => χ x ^ 2 * sourceConnectionCross d (naturalCanonicalFlux d g) Du x /
      radialDenom δ (fun a => naturalCanonicalFlux d g a x)) (potentialMeasure d.potential) ∧
    Integrable (fun x => χ x ^ 2 * sourceRadialExtra d (naturalCanonicalFlux d g) Du x /
      radialDenom δ (fun a => naturalCanonicalFlux d g a x) ^ 2) (potentialMeasure d.potential) ∧
    Integrable (fun x => χ x * sourceConnectionBoundary d χ (naturalCanonicalFlux d g) x /
      radialDenom δ (fun a => naturalCanonicalFlux d g a x)) (potentialMeasure d.potential) ∧
    Integrable (fun x => χ x ^ 2 * sourceVectorMass d.potential (naturalCanonicalFlux d g) x /
      radialDenom δ (fun a => naturalCanonicalFlux d g a x)) (potentialMeasure d.potential) ∧
    Integrable (fun x => χ x ^ 2 * sourceConnectionTarget d (naturalCanonicalFlux d g) x /
      radialDenom δ (fun a => naturalCanonicalFlux d g a x)) (potentialMeasure d.potential) ∧
    Integrable (fun x => χ x ^ 2 * sourceConnectionGamma d (naturalCanonicalFlux d g) x /
      radialDenom δ (fun a => naturalCanonicalFlux d g a x)) (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let ν := potentialMeasure d.potential
  let u := naturalCanonicalFlux d g
  let f (x : Space n) := radialDenom δ (fun a => u a x)
  let v := radialBoundedVector δ u
  have hv (i : Fin n) : MemLp (v i) ∞ ν :=
    radialBoundedVector_memLp_top_source d hδ (naturalCanonicalFlux_aestronglyMeasurable d g) i
  have hvloc (i : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (v i) ∞ (volume.restrict E) :=
    KLS.MemLp.restrict_volume_of_potentialMeasure (hv i) d.source_C1.continuous hE
  have hχtop : MemLp χ ∞ ν := hχ.continuous.memLp_of_hasCompactSupport hc
  have hχ2top : MemLp (fun x => χ x ^ 2) ∞ ν := by
    have hm : MemLp (χ * χ) ∞ ν := hχtop.mul hχtop
    change MemLp (fun x => χ x * χ x) ∞ ν at hm
    simpa only [pow_two] using hm
  have hcn (i : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => u i x / f x) ∞ (volume.restrict E) :=
    KLS.MemLp.restrict_volume_of_potentialMeasure (radial_natural_coordinate_memLp_top d g hδ i)
      d.source_C1.continuous hE
  have htn (i j k : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => (u i x * u j x * u k x) / f x ^ 2) ∞ (volume.restrict E) :=
    KLS.MemLp.restrict_volume_of_potentialMeasure (radial_natural_triple_memLp_top d g hδ i j k)
      d.source_C1.continuous hE
  have hX (i j a : Fin n) : Integrable (fun x => χ x ^ 2 *
      (((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
        (Du i a x * u j x + u i x * Du j a x)) / f x) ν := by
    have h1 : LocallyIntegrable (fun x =>
        (((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j * Du i a x) *
          (u j x / f x)) volume := by
      apply locallyIntegrable_iff.mpr
      intro E hE
      have hi := ((actual_connection_flux_local_L2 d i a j E hE).integrable_mul (hDu i a E hE)).mul_of_top_right
        (hcn j E hE)
      apply hi.congr
      exact Eventually.of_forall fun x => mul_comm _ _
    have h2 : LocallyIntegrable (fun x =>
        (((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j * Du j a x) *
          (u i x / f x)) volume := by
      apply locallyIntegrable_iff.mpr
      intro E hE
      have hi := ((actual_connection_flux_local_L2 d i a j E hE).integrable_mul (hDu j a E hE)).mul_of_top_right
        (hcn i E hE)
      apply hi.congr
      exact Eventually.of_forall fun x => mul_comm _ _
    have hi := integrable_raw_mul_compact_potential d.source_C1.continuous (h1.add h2)
      (hχ.pow 2).continuous (by simpa only [pow_two, Pi.mul_def] using hc.mul_right (f' := χ))
    apply hi.congr
    exact Eventually.of_forall fun x => by
      change ((_ + _) * χ x ^ 2) = _
      dsimp only [Pi.add_apply]
      ring
  have hE (i j a k : Fin n) : Integrable (fun x => χ x ^ 2 *
      (((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
        (u i x * u j x) * (u k x * Du k a x)) / f x ^ 2) ν := by
    have hl : LocallyIntegrable (fun x =>
        (((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j * Du k a x) *
          ((u i x * u j x * u k x) / f x ^ 2)) volume := by
      apply locallyIntegrable_iff.mpr
      intro E hE
      have hi := ((actual_connection_flux_local_L2 d i a j E hE).integrable_mul (hDu k a E hE)).mul_of_top_right
        (htn i j k E hE)
      apply hi.congr
      exact Eventually.of_forall fun x => mul_comm _ _
    have hi := integrable_raw_mul_compact_potential d.source_C1.continuous hl
      (hχ.pow 2).continuous (by simpa only [pow_two, Pi.mul_def] using hc.mul_right (f' := χ))
    apply hi.congr
    exact Eventually.of_forall fun x => by dsimp only; ring
  have hB : Integrable (fun x => χ x * sourceConnectionBoundary d χ u x / f x) ν := by
    have hb : Integrable (fun x => χ x * sourceConnectionBoundary d χ v x) ν := by
      simpa only [sourceConnectionBoundary, Finset.mul_sum] using
        integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ =>
          integrable_finsetSum Finset.univ (fun a _ =>
            (compact_connection_boundary_summand_memLp d hvloc hχ hc i j a).integrable (by norm_num))))
    apply hb.congr
    exact Eventually.of_forall fun x => by
      change χ x * sourceConnectionBoundary d χ (radialBoundedVector δ u) x =
        χ x * sourceConnectionBoundary d χ u x / f x
      rw [(radialBoundedVector_contractions hδ.le d u χ x).2.2]
      ring
  have hM : MemLp (fun x => (sourceVectorMass d.potential u x / f x) * χ x ^ 2) ∞ ν :=
    (actual_radial_mass_memLp_top d g hδ).mul hχ2top
  have hP : Integrable (sourceConnectionTarget d v) ν := by
    apply integrable_finsetSum Finset.univ
    intro i _
    apply integrable_finsetSum Finset.univ
    intro j _
    have h1 : MemLp (fun x => sourceTargetCurvature d x i j * v i x) ∞ ν :=
      (actual_target_curvature_entry_memLp_top d i j).mul (hv i)
    have h2 : MemLp (fun x => sourceTargetCurvature d x i j * v i x * v j x) ∞ ν := h1.mul (hv j)
    exact h2.integrable (by norm_num)
  have hG := (actual_radial_connectionGamma_integrable d g hδ).mul_of_top_right hχ2top
  refine ⟨?_, ?_, hB, ?_, ?_, ?_⟩
  · simpa only [sourceConnectionCross, Finset.mul_sum, Finset.sum_div] using
      integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ =>
        integrable_finsetSum Finset.univ (fun a _ => hX i j a)))
  · simpa only [sourceRadialExtra, Finset.mul_sum, Finset.sum_div] using
      integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ =>
        integrable_finsetSum Finset.univ (fun a _ => integrable_finsetSum Finset.univ (fun k _ => hE i j a k))))
  · apply (hM.integrable (by norm_num)).congr
    exact Eventually.of_forall fun x => by dsimp only [Pi.mul_apply]; ring
  · have he (x : Space n) : sourceConnectionTarget d v x = sourceConnectionTarget d u x / f x := by
      simp only [sourceConnectionTarget, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_assoc, radialBoundedVector_product hδ.le]
      ring
    apply (hP.mul_of_top_right hχ2top).congr
    exact Eventually.of_forall fun x => by
      change χ x ^ 2 * sourceConnectionTarget d v x = χ x ^ 2 * sourceConnectionTarget d u x / f x
      rw [he]
      ring
  · apply hG.congr
    exact Eventually.of_forall fun x => by dsimp only [Pi.mul_apply]; ring

end KLSConstantImprovement.ActualSourceRadialConnectionDomains405
#print axioms KLSConstantImprovement.ActualSourceRadialConnectionDomains405.sourceRadialExtra_contraction
#print axioms KLSConstantImprovement.ActualSourceRadialConnectionDomains405.radial_natural_coordinate_memLp_top
#print axioms KLSConstantImprovement.ActualSourceRadialConnectionDomains405.radial_natural_triple_memLp_top
#print axioms KLSConstantImprovement.ActualSourceRadialConnectionDomains405.actual_compact_radial_connection_fields_integrable

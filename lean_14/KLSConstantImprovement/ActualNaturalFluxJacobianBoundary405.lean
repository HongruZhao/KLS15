import KLSConstantImprovement.ActualSourceRadialConnectionBoundary405
import KLSConstantImprovement.ActualCompatibleConnectionBoundary405
import KLSConstantImprovement.ActualSourceBoundedMassGammaDomain405
import KLSConstantImprovement.ActualPotentialWeakTests405

/-! The actual compatible Jacobian pays a global target-row flux and its
spatial boundary.  The column error is controlled by Q times the unweighted
metric cutoff energy, rather than by the unproved bounded natural mass. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualNaturalFluxJacobianBoundary405
open KLS ActualBoundedCanonicalSource ActualSourceLocalizedGaffney405
open ActualSourceConnectionPointwise405 ActualSourceRadialConnectionBoundary405
open ActualCompatibleConnectionBoundary405 ActualSquareDominatedBoundaryLimit405
open ActualWeakCanonicalMetricCutoffs ActualSourceBoundedMassGammaDomain405
open ActualPotentialWeakTests405 ActualSourceCompactConnectionAbsorption405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem compatible_column_square (H B : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (hB : (H * B).IsSymm) (z : Fin n → ℝ) (j : Fin n) :
    (∑ i, B i j * z i) ^ 2 ≤
      (z ⬝ᵥ (H⁻¹ *ᵥ z)) * H j j * (B * B).trace := by
  have hInv : H⁻¹ * H = 1 :=
    Matrix.nonsing_inv_mul H ((Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit)
  have hJB : H⁻¹ * (H * B) = B := by rw [← Matrix.mul_assoc, hInv, Matrix.one_mul]
  have ht : (H⁻¹ * (H * B) * H⁻¹ * (H * B)).trace = (B * B).trace := by
    calc
      _ = ((H⁻¹ * (H * B)) * (H⁻¹ * (H * B))).trace := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hJB]
  have hvec : H⁻¹ *ᵥ ((H * B) *ᵥ Pi.single j 1) = B *ᵥ Pi.single j 1 := by
    rw [Matrix.mulVec_mulVec, hJB]
  have hm : Pi.single j (1 : ℝ) ⬝ᵥ (H *ᵥ Pi.single j 1) = H j j := by
    simp only [Matrix.mulVec_single_one, single_one_dotProduct, Matrix.col_apply]
  have he := compatible_connection_boundary_square H (H * B) hH hB z (Pi.single j 1)
  rw [hvec, ht, hm] at he
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, dotProduct, mul_comm] using he

theorem compatible_flux_entry_square (H B : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (hB : (H * B).IsSymm) (i j : Fin n) :
    (H * B) i j ^ 2 ≤ H i i * H j j * (B * B).trace := by
  have hInv : H⁻¹ * H = 1 :=
    Matrix.nonsing_inv_mul H ((Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit)
  have hz : (H *ᵥ Pi.single i (1 : ℝ)) ⬝ᵥ
      (H⁻¹ *ᵥ (H *ᵥ Pi.single i 1)) = H i i := by
    rw [Matrix.mulVec_mulVec, hInv, Matrix.one_mulVec, dotProduct_comm,
      Matrix.mulVec_single_one, single_one_dotProduct, Matrix.col_apply]
  have hl : (∑ a : Fin n, B a j * (H *ᵥ Pi.single i 1) a) = (H * B) i j := by
    simp only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro a _
    rw [hH.isHermitian.isSymm.apply i a]
    ring
  have he := compatible_column_square H B hH hB (H *ᵥ Pi.single i 1) j
  rwa [hz, hl] at he

def compatibleTargetFlux (d : SourceData μ)
    (Du : Fin n → Fin n → Space n → ℝ) (j a : Fin n) (x : Space n) : ℝ :=
  (coordinateHessian d.potential x * Matrix.of (fun i k => Du i k x)) j a

theorem compatibleTargetFlux_memLp (d : SourceData μ)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hDu : ∀ i j E, IsCompact E → MemLp (Du i j) 2 (volume.restrict E))
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i j => Du i j x)).IsSymm)
    (hQi : Integrable (sourceVectorJacobianEnergy Du) (potentialMeasure d.potential))
    (j a : Fin n) :
    MemLp (compatibleTargetFlux d Du j a) 2 (potentialMeasure d.potential) := by
  let ν := potentialMeasure d.potential
  have hloc (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (compatibleTargetFlux d Du j a) 2 (volume.restrict E) := by
    unfold compatibleTargetFlux
    simp only [Matrix.mul_apply, Matrix.of_apply]
    apply memLp_finsetSum Finset.univ
    intro i _
    exact (KLS.MemLp.restrict_volume_of_potentialMeasure (d.hessian_entry_memLp j i ∞)
      d.source_C1.continuous hE).mul (hDu i a E hE)
  have hm : AEStronglyMeasurable (compatibleTargetFlux d Du j a) ν :=
    (locallyIntegrable_of_memLp_two_on_compacts hloc).aestronglyMeasurable.mono_ac
      (withDensity_absolutelyContinuous _ _)
  let Cj := lpNorm (fun x => coordinateHessian d.potential x j j) ∞ ν
  let Ca := lpNorm (fun x => coordinateHessian d.potential x a a) ∞ ν
  have hCj : 0 ≤ Cj := lpNorm_nonneg
  have hCa : 0 ≤ Ca := lpNorm_nonneg
  have hj := ae_le_lpNorm_exponent_top (d.hessian_entry_memLp j j ∞)
  have ha := ae_le_lpNorm_exponent_top (d.hessian_entry_memLp a a ∞)
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply (hQi.const_mul (Cj * Ca)).mono' (hm.pow 2)
  have hac : ν ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source, hcomp.filter_mono hac.ae_le, hj, ha,
    sourceVectorJacobianEnergy_nonnegative_ae d Du hcomp] with x hp hc hJ hA hQ
  change ‖compatibleTargetFlux d Du j a x ^ 2‖ ≤ Cj * Ca * sourceVectorJacobianEnergy Du x
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hjb : coordinateHessian d.potential x j j ≤ Cj :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hJ)
  have hab : coordinateHessian d.potential x a a ≤ Ca :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hA)
  have he := compatible_flux_entry_square (coordinateHessian d.potential x)
    (Matrix.of (fun i k => Du i k x)) hp.1 hc j a
  have hqeq : (Matrix.of (fun i k => Du i k x) * Matrix.of (fun i k => Du i k x)).trace =
      sourceVectorJacobianEnergy Du x := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply,
      sourceVectorJacobianEnergy]
  rw [hqeq] at he
  have hh : coordinateHessian d.potential x j j * coordinateHessian d.potential x a a ≤ Cj * Ca :=
    mul_le_mul hjb hab hp.1.posSemidef.diag_nonneg hCj
  exact he.trans (mul_le_mul_of_nonneg_right hh hQ)

theorem exists_compatible_column_target_boundary_cutoffs (d : SourceData μ)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hDu : ∀ i j E, IsCompact E → MemLp (Du i j) 2 (volume.restrict E))
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i j => Du i j x)).IsSymm)
    (hQi : Integrable (sourceVectorJacobianEnergy Du) (potentialMeasure d.potential))
    {f : Space n → ℝ} (hf : Continuous f) (j : Fin n) :
    ∃ χ : ℕ → Space n → ℝ,
      (∀ k, ContDiff ℝ 1 (χ k) ∧ HasCompactSupport (χ k) ∧ ∀ x, χ k x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x, Tendsto (fun k => χ k x) atTop (𝓝 1)) ∧
      (∀ k, Integrable (fun x => f (gradient d.potential x) *
        (∑ i : Fin n, Du i j x * coordinateDerivative (χ k) i x)) (potentialMeasure d.potential)) ∧
      Tendsto (fun k => ∫ x, |f (gradient d.potential x) *
        (∑ i : Fin n, Du i j x * coordinateDerivative (χ k) i x)| ∂potentialMeasure d.potential)
        atTop (𝓝 0) ∧
      Tendsto (fun k => ∫ x, f (gradient d.potential x) *
        (∑ i : Fin n, Du i j x * coordinateDerivative (χ k) i x) ∂potentialMeasure d.potential)
        atTop (𝓝 0) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let ν := potentialMeasure d.potential
  obtain ⟨B, hB, hb⟩ := d.exists_bound_continuous_comp_gradient hf
  let C := lpNorm (fun x => coordinateHessian d.potential x j j) ∞ ν
  have hC : 0 ≤ C := lpNorm_nonneg
  have hH : ∀ᵐ x ∂ν, coordinateHessian d.potential x j j ≤ C := by
    filter_upwards [ae_le_lpNorm_exponent_top (d.hessian_entry_memLp j j ∞)] with x hx
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hx)
  obtain ⟨x₀, _, hc, _, hp, _, _, hEi, hElim⟩ := d.exists_metric_energy_cutoffs
  let χ := hessianMetricCutoffSequence d.potential x₀
  have hBi (k : ℕ) : Integrable (fun x => f (gradient d.potential x) *
      (∑ i : Fin n, Du i j x * coordinateDerivative (χ k) i x)) ν := by
    have hi (i : Fin n) : Integrable (fun x => Du i j x *
        (f (gradient d.potential x) * coordinateDerivative (χ k) i x)) ν :=
      integrable_raw_mul_compact_potential d.source_C1.continuous
        (locallyIntegrable_of_memLp_two_on_compacts (fun E hE => hDu i j E hE))
        ((hf.comp d.gradient_lipschitz.continuous).mul
          (contDiff_coordinateDerivative (hc k).1 (m := 0) (by norm_num) i).continuous)
        ((hasCompactSupport_coordinateDerivative (hc k).2.1 i).mul_left)
    apply (integrable_finsetSum Finset.univ (fun i _ => hi i)).congr
    exact Eventually.of_forall fun x => by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
  have he0 (k : ℕ) : ∀ᵐ x ∂ν,
      0 ≤ (B ^ 2 * C) * inverseHessianGradientForm d.potential (χ k) x :=
    d.hessian_ae_source.mono fun x hx => mul_nonneg (by positivity)
      (inverseHessianGradientForm_nonneg_at (χ k) hx.1)
  have hs (k : ℕ) : ∀ᵐ x ∂ν, (f (gradient d.potential x) *
      (∑ i : Fin n, Du i j x * coordinateDerivative (χ k) i x)) ^ 2 ≤
      ((B ^ 2 * C) * inverseHessianGradientForm d.potential (χ k) x) * sourceVectorJacobianEnergy Du x := by
    have hac : ν ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
    filter_upwards [d.hessian_ae_source, hcomp.filter_mono hac.ae_le, hH,
      sourceVectorJacobianEnergy_nonnegative_ae d Du hcomp] with x hx hD hh hQ
    have hE : 0 ≤ inverseHessianGradientForm d.potential (χ k) x :=
      inverseHessianGradientForm_nonneg_at (χ k) hx.1
    have hsq : f (gradient d.potential x) ^ 2 ≤ B ^ 2 := by
      have hn := hb x
      rw [Real.norm_eq_abs] at hn
      nlinarith [sq_abs (f (gradient d.potential x)), abs_nonneg (f (gradient d.potential x))]
    have he := compatible_column_square (coordinateHessian d.potential x)
      (Matrix.of (fun i a => Du i a x)) hx.1 hD
      (fun i => coordinateDerivative (χ k) i x) j
    have hqeq : (Matrix.of (fun i a => Du i a x) * Matrix.of (fun i a => Du i a x)).trace =
        sourceVectorJacobianEnergy Du x := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply,
        sourceVectorJacobianEnergy]
    rw [hqeq, ← matrix_quadratic_sum_eq_dotProduct] at he
    change (∑ i : Fin n, Du i j x * coordinateDerivative (χ k) i x) ^ 2 ≤
      inverseHessianGradientForm d.potential (χ k) x * coordinateHessian d.potential x j j *
        sourceVectorJacobianEnergy Du x at he
    rw [mul_pow]
    calc
      _ ≤ B ^ 2 * (inverseHessianGradientForm d.potential (χ k) x *
          coordinateHessian d.potential x j j * sourceVectorJacobianEnergy Du x) :=
        mul_le_mul hsq he (sq_nonneg _) (sq_nonneg B)
      _ ≤ _ := by
        have hh' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hE) hQ
        have hh'' := mul_le_mul_of_nonneg_left hh' (sq_nonneg B)
        simpa only [mul_comm, mul_left_comm, mul_assoc] using hh''
  have helim : Tendsto (fun k => ∫ x, (B ^ 2 * C) *
      inverseHessianGradientForm d.potential (χ k) x ∂ν) atTop (𝓝 0) := by
    simpa only [integral_const_mul, mul_zero] using hElim.const_mul (B ^ 2 * C)
  obtain ⟨habs, hsign⟩ := integral_tendsto_zero_of_square_domination hBi
    (fun k => (hEi k).const_mul (B ^ 2 * C)) hQi he0
    (sourceVectorJacobianEnergy_nonnegative_ae d Du hcomp) hs helim
  exact ⟨χ, hc, hp, hBi, habs, hsign⟩

end KLSConstantImprovement.ActualNaturalFluxJacobianBoundary405
#print axioms KLSConstantImprovement.ActualNaturalFluxJacobianBoundary405.compatible_column_square
#print axioms KLSConstantImprovement.ActualNaturalFluxJacobianBoundary405.compatible_flux_entry_square
#print axioms KLSConstantImprovement.ActualNaturalFluxJacobianBoundary405.compatibleTargetFlux_memLp
#print axioms KLSConstantImprovement.ActualNaturalFluxJacobianBoundary405.exists_compatible_column_target_boundary_cutoffs

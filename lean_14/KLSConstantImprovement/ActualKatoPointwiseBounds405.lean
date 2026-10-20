import KLSConstantImprovement.ActualRegularizedWeakBochner405

/-! The positive actual covariant density and the metric gradient bound
of the literal forcing imply the regularized Kato pointwise inequalities. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualKatoPointwiseBounds405
open KLS ActualBoundedCanonicalSource ActualKatoJointPointwise405 ActualKatoNonlinearDomains405
open ActualKatoLocalDomains405 ActualNaturalCovariantEnergy405 ActualSmoothKatoRegularizer405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405 ActualSourceConnectionFields405
open ActualSourceConnectionPointwise405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
variable {n : ℕ} {μ : Measure (Space n)}

theorem finite_inverse_metric_forcing_bound (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (u v : Fin n → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hv : v ⬝ᵥ (H⁻¹ *ᵥ v) ≤ B ^ 2) :
    u ⬝ᵥ v ≤ Real.sqrt (u ⬝ᵥ (H *ᵥ u)) * B := by
  let M := u ⬝ᵥ (H *ᵥ u)
  have hM : 0 ≤ M := hH.posSemidef.dotProduct_mulVec_nonneg _
  have hInv : H * H⁻¹ = 1 :=
    Matrix.mul_nonsing_inv H ((Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit)
  have heq : H *ᵥ (H⁻¹ *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hInv, Matrix.one_mulVec]
  have hc := hH.star_dotProduct_mulVec_mul_le u (H⁻¹ *ᵥ v)
  simp only [star_trivial, heq] at hc
  have hcomm : (H⁻¹ *ᵥ v) ⬝ᵥ v = v ⬝ᵥ (H⁻¹ *ᵥ v) := dotProduct_comm _ _
  rw [hcomm] at hc
  have hcs : (u ⬝ᵥ v) ^ 2 ≤ M * (v ⬝ᵥ (H⁻¹ *ᵥ v)) := by
    simpa only [pow_two] using hc
  have hs : (u ⬝ᵥ v) ^ 2 ≤ M * B ^ 2 :=
    hcs.trans (mul_le_mul_of_nonneg_left hv hM)
  have hroot : 0 ≤ Real.sqrt M * B := mul_nonneg (Real.sqrt_nonneg _) hB
  have hsq : |u ⬝ᵥ v| ^ 2 ≤ (Real.sqrt M * B) ^ 2 := by
    rw [sq_abs, mul_pow, Real.sq_sqrt hM]
    exact hs
  exact (le_abs_self _).trans ((sq_le_sq₀ (abs_nonneg _) hroot).mp hsq)

theorem naturalKatoForcing_upper_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (Dg : Fin n → Space n → ℝ)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε)
    (hgrad : ∀ᵐ x ∂potentialMeasure d.potential,
      (fun a => Dg a x) ⬝ᵥ ((coordinateHessian d.potential x)⁻¹ *ᵥ (fun a => Dg a x)) ≤ B ^ 2) :
    ∀ᵐ x ∂potentialMeasure d.potential, naturalKatoForcing d g ε Dg x ≤ B := by
  filter_upwards [d.hessian_ae_source, natural_mass_nonnegative_ae d g, hgrad] with x hH hM hG
  have hm : (fun a => naturalCanonicalFlux d g a x) ⬝ᵥ
      (coordinateHessian d.potential x *ᵥ (fun a => naturalCanonicalFlux d g a x)) =
        sourceVectorMass d.potential (naturalCanonicalFlux d g) x :=
    (matrix_quadratic_sum_eq_dotProduct _ _).symm
  have hf := finite_inverse_metric_forcing_bound (coordinateHessian d.potential x) hH.1
    (fun a => naturalCanonicalFlux d g a x) (fun a => Dg a x) hB hG
  rw [hm] at hf
  obtain ⟨hfp, _hc, hb, _hm⟩ := katoRegularizer_coefficient_bounds hε hM
  have he : (∑ a : Fin n, Dg a x * naturalCanonicalFlux d g a x) =
      (fun a => naturalCanonicalFlux d g a x) ⬝ᵥ (fun a => Dg a x) := by
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  unfold naturalKatoForcing
  rw [he]
  calc
    _ ≤ 2 * katoFirst ε (sourceVectorMass d.potential (naturalCanonicalFlux d g) x) *
        (Real.sqrt (sourceVectorMass d.potential (naturalCanonicalFlux d g) x) * B) :=
      mul_le_mul_of_nonneg_left hf (by positivity)
    _ = (2 * katoFirst ε (sourceVectorMass d.potential (naturalCanonicalFlux d g) x) *
        Real.sqrt (sourceVectorMass d.potential (naturalCanonicalFlux d g) x)) * B := by ring
    _ ≤ B := mul_le_of_le_one_left hB hb

theorem naturalKatoDensity_lower_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i a => Du i a x)).IsSymm)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      naturalKatoValue d g ε x / 2 - Real.sqrt ε / 2 ≤ naturalKatoDensity d g Du ε x := by
  filter_upwards [d.hessian_ae_source, natural_mass_nonnegative_ae d g,
    natural_covariant_energy_nonnegative_ae d g Du hcomp,
    sourceConnectionTarget_nonnegative_ae d (naturalCanonicalFlux d g),
    sourceConnectionGamma_nonnegative_ae d (naturalCanonicalFlux d g),
    natural_covariant_mass_kato_ae d g Du hcomp,
    natural_Bochner_density_covariant_ae d g Du] with x hH hM hE hP hΓ hD hBo
  have hDn : 0 ≤ naturalMassMetricSquare d g Du x := hH.1.inv.posSemidef.dotProduct_mulVec_nonneg _
  have he := katoRegularizer_chain_density_lower hε hM hE hP hΓ hDn hD
  unfold naturalKatoValue naturalKatoDensity
  rw [hBo]
  exact he

end KLSConstantImprovement.ActualKatoPointwiseBounds405
#print axioms KLSConstantImprovement.ActualKatoPointwiseBounds405.finite_inverse_metric_forcing_bound
#print axioms KLSConstantImprovement.ActualKatoPointwiseBounds405.naturalKatoForcing_upper_ae
#print axioms KLSConstantImprovement.ActualKatoPointwiseBounds405.naturalKatoDensity_lower_ae

import KLSConstantImprovement.ActualNaturalCovariantEnergy405
import KLSConstantImprovement.ActualSmoothKatoRegularizer405

/-! The literal half-mass flux and the finite regularized Kato energy.
The actual weak derivative is retained; no classical derivative of H or
nonlinear weak chain rule is asserted in these finite identities. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualKatoFluxAlgebra405
open KLS ActualBoundedCanonicalSource ActualCovariantKatoAlgebra405
open ActualNaturalMassWeakDerivative405 ActualNaturalCovariantEnergy405 ActualSmoothKatoRegularizer405
open ActualJointWeakBochner405 ActualJointBochnerContractions405 ActualSourceNaturalGaffney405
open ActualSourceLocalizedGaffney405 ActualSourceConnectionFields405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem inverse_covariant_half_mass_flux (H B N : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (u : Fin n → ℝ) (a : Fin n) :
    (H⁻¹ *ᵥ ((2 : ℝ) • (covariantHessian H B N *ᵥ u))) a / 2 =
      (B *ᵥ u) a + (H⁻¹ *ᵥ (N *ᵥ u)) a / 2 := by
  have hInv : H⁻¹ * H = 1 :=
    Matrix.nonsing_inv_mul H ((Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit)
  have hA : H⁻¹ * covariantHessian H B N = B + (1/2 : ℝ) • (H⁻¹ * N) := by
    unfold covariantHessian
    rw [Matrix.mul_add, ← Matrix.mul_assoc, hInv, Matrix.one_mul, Matrix.mul_smul]
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hA, Matrix.add_mulVec,
    Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

theorem natural_half_mass_flux_eq_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i a => Du i a x)).IsSymm) :
    ∀ᵐ x ∂potentialMeasure d.potential, ∀ a : Fin n,
      sourceHalfMassFlux d (ActualSourceNaturalGaffney405.naturalCanonicalFlux d g) Du a x =
        ((coordinateHessian d.potential x)⁻¹ *ᵥ (fun b => naturalMassRawDerivative d g Du b x)) a / 2 := by
  filter_upwards [d.hessian_ae_source, natural_mass_derivative_covariant_ae d g Du hcomp]
    with x hH hD
  have hvec : (fun b => naturalMassRawDerivative d g Du b x) =
      (2 : ℝ) • (naturalCovariantHessian d g Du x *ᵥ
        (fun i => ActualSourceNaturalGaffney405.naturalCanonicalFlux d g i x)) := by
    funext b
    exact hD b
  intro a
  rw [hvec]
  have he := inverse_covariant_half_mass_flux (coordinateHessian d.potential x)
    (Matrix.of (fun i b => Du i b x))
    (sourceThirdAlong d (ActualSourceNaturalGaffney405.naturalCanonicalFlux d g) x)
    hH.1 (fun i => ActualSourceNaturalGaffney405.naturalCanonicalFlux d g i x) a
  simpa only [naturalCovariantHessian, sourceHalfMassFlux, rowMassFlux,
    Matrix.mulVec, dotProduct, Matrix.of_apply] using he.symm

theorem vector_coordinate_square_le_inverse_energy (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (z : Fin n → ℝ) (a : Fin n) :
    z a ^ 2 ≤ H a a * (z ⬝ᵥ (H⁻¹ *ᵥ z)) := by
  have hInv : H * H⁻¹ = 1 :=
    Matrix.mul_nonsing_inv H ((Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit)
  have hz : H *ᵥ (H⁻¹ *ᵥ z) = z := by rw [Matrix.mulVec_mulVec, hInv, Matrix.one_mulVec]
  have hc := hH.star_dotProduct_mulVec_mul_le (Pi.single a 1) (H⁻¹ *ᵥ z)
  simp only [star_trivial, hz, single_one_dotProduct, Matrix.mulVec_single_one,
    Matrix.col_apply, pow_two] at hc
  have hsym : (H⁻¹ *ᵥ z) ⬝ᵥ z = z ⬝ᵥ (H⁻¹ *ᵥ z) := dotProduct_comm _ _
  simpa only [hsym, pow_two] using hc

theorem katoFirst_energy_bound {ε M E D : ℝ}
    (hε : 0 < ε) (hM : 0 ≤ M) (hE : 0 ≤ E) (hD : D ≤ 4 * M * E) :
    katoFirst ε M ^ 2 * D ≤ E := by
  obtain ⟨hf, _hc, hb, _hm⟩ := katoRegularizer_coefficient_bounds hε hM
  have hbn : 0 ≤ 2 * katoFirst ε M * Real.sqrt M := by positivity
  have hb2 : (2 * katoFirst ε M * Real.sqrt M) ^ 2 ≤ (1 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hbn hb 2
  simp only [mul_pow, Real.sq_sqrt hM] at hb2
  have hfac : katoFirst ε M ^ 2 * (4 * M) ≤ 1 := by nlinarith only [hb2]
  have h1 := mul_le_mul_of_nonneg_left hD (sq_nonneg (katoFirst ε M))
  have h2 := mul_le_mul_of_nonneg_right hfac hE
  nlinarith only [h1, h2]

theorem regularized_mass_gradient_energy (H : Matrix (Fin n) (Fin n) ℝ)
    {ε M E : ℝ} (hH : H.PosDef) (hε : 0 < ε) (hM : 0 ≤ M) (hE : 0 ≤ E)
    (z : Fin n → ℝ) (hz : z ⬝ᵥ (H⁻¹ *ᵥ z) ≤ 4 * M * E) :
    ((katoFirst ε M) • z) ⬝ᵥ (H⁻¹ *ᵥ ((katoFirst ε M) • z)) ≤ E ∧
      ∀ a : Fin n, (katoFirst ε M * z a) ^ 2 ≤ H a a * E := by
  have he := katoFirst_energy_bound hε hM hE hz
  have hscale : ((katoFirst ε M) • z) ⬝ᵥ (H⁻¹ *ᵥ ((katoFirst ε M) • z)) =
      katoFirst ε M ^ 2 * (z ⬝ᵥ (H⁻¹ *ᵥ z)) := by
    simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  refine ⟨by rw [hscale]; exact he, ?_⟩
  intro a
  have hc := vector_coordinate_square_le_inverse_energy H hH ((katoFirst ε M) • z) a
  rw [hscale] at hc
  exact hc.trans (mul_le_mul_of_nonneg_left he hH.posSemidef.diag_nonneg)

end KLSConstantImprovement.ActualKatoFluxAlgebra405
#print axioms KLSConstantImprovement.ActualKatoFluxAlgebra405.inverse_covariant_half_mass_flux
#print axioms KLSConstantImprovement.ActualKatoFluxAlgebra405.natural_half_mass_flux_eq_ae
#print axioms KLSConstantImprovement.ActualKatoFluxAlgebra405.vector_coordinate_square_le_inverse_energy
#print axioms KLSConstantImprovement.ActualKatoFluxAlgebra405.katoFirst_energy_bound
#print axioms KLSConstantImprovement.ActualKatoFluxAlgebra405.regularized_mass_gradient_energy

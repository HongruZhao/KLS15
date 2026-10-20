import KLSConstantImprovement.ActualNaturalMassWeakDerivative405
import KLSConstantImprovement.ActualJointWeakBochner405
import KLS.WeakMatrixProduct
import KLS.WeakHessianInverseDerivative

/-! The actual covariant Hessian energy is locally L1 and controls the
literal weak mass derivative. The positive Gamma2 used in common-joint
Bochner testing is identified with this actual square. No mass bound or
classical derivative of the source Hessian is assumed. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualNaturalCovariantEnergy405
open KLS ActualBoundedCanonicalSource ActualNaturalMassWeakDerivative405 ActualNaturalLocalHessianDomain405
open ActualCovariantKatoAlgebra405 ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
open ActualSourceConnectionFields405 ActualSourceConnectionPointwise405 ActualSourceNaturalHessian405
open ActualNaturalLocalConnectionDomain405 ActualJointWeakBochner405
open ActualCompatibleConnectionYoung405 ActualSourceHessianEvolution405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

def naturalCovariantEnergy (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) (x : Space n) : ℝ :=
  ((coordinateHessian d.potential x)⁻¹ * naturalCovariantHessian d g Du x *
    (coordinateHessian d.potential x)⁻¹ * naturalCovariantHessian d g Du x).trace

theorem finite_covariant_energy_eq (H B N : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef) :
    (H⁻¹ * covariantHessian H B N * H⁻¹ * covariantHessian H B N).trace =
      (B * B).trace + (B * H⁻¹ * N).trace + (H⁻¹ * N * H⁻¹ * N).trace / 4 := by
  let J := H⁻¹
  have hJH : J * H = 1 := Matrix.nonsing_inv_mul H ((Matrix.isUnit_iff_isUnit_det _).mp hH.isUnit)
  have hA : J * covariantHessian H B N = B + (1/2 : ℝ) • (J * N) := by
    unfold covariantHessian
    rw [Matrix.mul_add, ← Matrix.mul_assoc, hJH, Matrix.one_mul, Matrix.mul_smul]
  have hcomm : ((J * N) * B).trace = (B * (J * N)).trace := Matrix.trace_mul_comm _ _
  change (J * covariantHessian H B N * J * covariantHessian H B N).trace = _
  rw [show J * covariantHessian H B N * J * covariantHessian H B N =
    (J * covariantHessian H B N) * (J * covariantHessian H B N) by simp only [Matrix.mul_assoc], hA]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  rw [hcomm]
  simp only [Matrix.mul_assoc]
  ring

theorem natural_covariant_energy_local_integrable (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i a E, IsCompact E → MemLp (Du i a) 2 (volume.restrict E))
    (hΓ : ∀ E, IsCompact E → Integrable (sourceConnectionGamma d (naturalCanonicalFlux d g)) (volume.restrict E)) :
    LocallyIntegrable (naturalCovariantEnergy d g Du) volume := by
  obtain ⟨hJ, _hDJ, _hwJ⟩ := actual_mongeAmpere_inverse_hasLocalWeakDerivative
    (T := sourceThirdMatrix d) d.source_C1 (d.target_smooth.of_le (by simp))
    d.gradient_lipschitz (d.hessian_ae.mono fun _ hx => hx.2.1)
    d.third_local_L2 d.third_weak_derivative
  have hC (i j : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (fun x => naturalCovariantHessian d g Du x i j) 2 (volume.restrict E) := by
    have hH (a b : Fin n) : MemLp (fun x => coordinateHessian d.potential x a b) ∞ (volume.restrict E) :=
      memLp_top_actual_hessian_of_locallyLipschitz_gradient d.gradient_lipschitz.locallyLipschitz a b hE
    have hHB : MemLp (fun x => (coordinateHessian d.potential x * Matrix.of (fun a b => Du a b x)) i j)
        2 (volume.restrict E) :=
      memLp_two_matrixMul_left hH (fun a b => hDu a b E hE) i j
    have hN := naturalThirdAlong_local_L2_of_local_Gamma d g hu hΓ i j E hE
    have hh := hHB.add (hN.const_mul (1/2 : ℝ))
    change MemLp (fun x => (coordinateHessian d.potential x * Matrix.of (fun a b => Du a b x)) i j +
      (1/2 : ℝ) * sourceThirdAlong d (naturalCanonicalFlux d g) x i j) 2 (volume.restrict E) at hh
    simpa only [naturalCovariantHessian, covariantHessian, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul] using hh
  apply locallyIntegrable_iff.mpr
  intro E hE
  let A (x : Space n) := (coordinateHessian d.potential x)⁻¹ * naturalCovariantHessian d g Du x
  have hA (i j : Fin n) : MemLp (fun x => A x i j) 2 (volume.restrict E) :=
    memLp_two_matrixMul_left (fun a b => hJ a b E hE) (fun a b => hC a b E hE) i j
  have hi : Integrable (fun x => ∑ i : Fin n, ∑ j : Fin n, A x i j * A x j i) (volume.restrict E) :=
    integrable_finsetSum Finset.univ fun i _ => integrable_finsetSum Finset.univ fun j _ =>
      (hA i j).integrable_mul (hA j i)
  apply hi.congr
  exact Eventually.of_forall fun x => by
    change (∑ i : Fin n, ∑ j : Fin n, A x i j * A x j i) = naturalCovariantEnergy d g Du x
    have hm : (coordinateHessian d.potential x)⁻¹ * naturalCovariantHessian d g Du x *
        (coordinateHessian d.potential x)⁻¹ * naturalCovariantHessian d g Du x = A x * A x := by
      dsimp only [A]
      simp only [Matrix.mul_assoc]
    simp only [naturalCovariantEnergy, hm, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

theorem natural_covariant_mass_kato_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i a => Du i a x)).IsSymm) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      (fun a => naturalMassRawDerivative d g Du a x) ⬝ᵥ
        ((coordinateHessian d.potential x)⁻¹ *ᵥ (fun a => naturalMassRawDerivative d g Du a x)) ≤
      4 * sourceVectorMass d.potential (naturalCanonicalFlux d g) x * naturalCovariantEnergy d g Du x := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source, hcomp.filter_mono hac.ae_le,
    sourceThirdAlong_isSymm_ae d (naturalCanonicalFlux d g), natural_mass_derivative_covariant_ae d g Du hcomp]
    with x hH hB hN hD
  have hvec : (fun a => naturalMassRawDerivative d g Du a x) =
      (2 : ℝ) • (naturalCovariantHessian d g Du x *ᵥ (fun i => naturalCanonicalFlux d g i x)) := by
    funext a
    exact hD a
  rw [hvec]
  have he := covariant_mass_derivative_kato (coordinateHessian d.potential x)
    (Matrix.of (fun i a => Du i a x)) (sourceThirdAlong d (naturalCanonicalFlux d g) x)
    hH.1 hB hN (fun i => naturalCanonicalFlux d g i x)
  simpa only [naturalCovariantHessian, naturalCovariantEnergy, sourceVectorMass,
    matrix_quadratic_sum_eq_dotProduct] using he

theorem natural_Bochner_density_covariant_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      sourceBochnerDensity d (naturalCanonicalFlux d g) Du x =
        naturalCovariantEnergy d g Du x +
          (sourceVectorMass d.potential (naturalCanonicalFlux d g) x +
            sourceConnectionTarget d (naturalCanonicalFlux d g) x) / 2 +
          sourceConnectionGamma d (naturalCanonicalFlux d g) x / 4 := by
  filter_upwards [d.hessian_ae_source,
    sourceConnectionCross_eq_trace_ae d (naturalCanonicalFlux d g) Du] with x hH hX
  have he := finite_covariant_energy_eq (coordinateHessian d.potential x)
    (Matrix.of (fun i a => Du i a x)) (sourceThirdAlong d (naturalCanonicalFlux d g) x) hH.1
  have hQ : ((Matrix.of (fun i a => Du i a x)) * (Matrix.of (fun i a => Du i a x))).trace =
      sourceVectorJacobianEnergy Du x := by
    simp only [sourceVectorJacobianEnergy, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
  rw [hQ, sourceThirdAlong_trace_square] at he
  change naturalCovariantEnergy d g Du x = _ at he
  dsimp only [sourceBochnerDensity]
  linarith

end KLSConstantImprovement.ActualNaturalCovariantEnergy405
#print axioms KLSConstantImprovement.ActualNaturalCovariantEnergy405.finite_covariant_energy_eq
#print axioms KLSConstantImprovement.ActualNaturalCovariantEnergy405.natural_covariant_energy_local_integrable
#print axioms KLSConstantImprovement.ActualNaturalCovariantEnergy405.natural_covariant_mass_kato_ae
#print axioms KLSConstantImprovement.ActualNaturalCovariantEnergy405.natural_Bochner_density_covariant_ae

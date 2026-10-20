import KLSConstantImprovement.ActualNaturalLocalHessianDomain405
import KLSConstantImprovement.ActualCovariantKatoAlgebra405

/-! The actual natural mass has a genuine local W1,1 derivative.  Its
covariant formula uses the compatible weak Gaffney Jacobian and the paid
local connection. No L2 or boundedness of the mass itself is assumed. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualNaturalMassWeakDerivative405
open KLS ActualBoundedCanonicalSource ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
open ActualSourceConnectionFields405 ActualSourceConnectionPointwise405
open ActualSourceNaturalTargetCurvatureDomain405 ActualSourceNaturalHessian405
open ActualNaturalLocalHessianDomain405 ActualCovariantKatoAlgebra405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

def naturalMassRawDerivative (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) (a : Fin n) (x : Space n) : ℝ :=
  ∑ i : Fin n, (Du i a x * naturalCanonicalRawGradient d g i x +
    naturalCanonicalFlux d g i x * naturalCanonicalHessian d g Du x i a)

def naturalCovariantHessian (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  covariantHessian (coordinateHessian d.potential x) (Matrix.of (fun i a => Du i a x))
    (sourceThirdAlong d (naturalCanonicalFlux d g) x)

theorem finite_mass_derivative_eq_covariant (H B N : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.IsSymm) (hB : (H * B).IsSymm) (hN : N.IsSymm) (u : Fin n → ℝ) (a : Fin n) :
    (∑ i : Fin n, (B i a * (H *ᵥ u) i + u i * (H * B + N) i a)) =
      2 * (covariantHessian H B N *ᵥ u) a := by
  have hBH : B.transpose * H = H * B := by
    simpa only [Matrix.transpose_mul, hH.eq] using hB.eq
  have hfirst : B.transpose *ᵥ (H *ᵥ u) = (H * B) *ᵥ u := by
    rw [Matrix.mulVec_mulVec, hBH]
  have hC : (H * B + N).IsSymm := by
    change (H * B + N).transpose = _
    rw [Matrix.transpose_add, hB.eq, hN.eq]
  calc
    _ = (B.transpose *ᵥ (H *ᵥ u)) a + ((H * B + N).transpose *ᵥ u) a := by
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    _ = ((H * B) *ᵥ u) a + ((H * B + N) *ᵥ u) a := by rw [hfirst, hC.eq]
    _ = _ := by
      simp only [Matrix.mulVec, dotProduct]
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [covariantHessian, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring

theorem natural_mass_derivative_local_integrable (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i a E, IsCompact E → MemLp (Du i a) 2 (volume.restrict E))
    (hC : ∀ i a E, IsCompact E → MemLp (fun x => naturalCanonicalHessian d g Du x i a) 2 (volume.restrict E))
    (a : Fin n) : LocallyIntegrable (naturalMassRawDerivative d g Du a) volume := by
  apply locallyIntegrable_iff.mpr
  intro E hE
  unfold naturalMassRawDerivative
  apply integrable_finsetSum Finset.univ
  intro i _
  have hp := KLS.MemLp.restrict_volume_of_potentialMeasure
    (naturalCanonicalRawGradient_memLp d g i) d.source_C1.continuous hE
  exact ((hDu i a E hE).integrable_mul hp).add ((hu i E hE).integrable_mul (hC i a E hE))

theorem natural_mass_hasLocalWeakDerivative (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i a E, IsCompact E → MemLp (Du i a) 2 (volume.restrict E))
    (hw : ∀ i a, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i a) a)
    (hC : ∀ i a E, IsCompact E → MemLp (fun x => naturalCanonicalHessian d g Du x i a) 2 (volume.restrict E))
    (a : Fin n) :
    HasLocalWeakCoordinateDerivative (sourceVectorMass d.potential (naturalCanonicalFlux d g))
      (naturalMassRawDerivative d g Du a) a := by
  let u := naturalCanonicalFlux d g
  let p := naturalCanonicalRawGradient d g
  have hp (i : Fin n) (E : Set (Space n)) (hE : IsCompact E) : MemLp (p i) 2 (volume.restrict E) :=
    KLS.MemLp.restrict_volume_of_potentialMeasure (naturalCanonicalRawGradient_memLp d g i)
      d.source_C1.continuous hE
  have hprod (i : Fin n) := (hw i a).mul
    (naturalRawGradient_weakHessian_without_mass d g Du hu hDu hw i a)
      (hu i) (hp i) (hDu i a) (hC i a)
  have hval (i : Fin n) : LocallyIntegrable (fun x => u i x * p i x) volume := by
    apply locallyIntegrable_iff.mpr
    intro E hE
    exact (hu i E hE).integrable_mul (hp i E hE)
  have hder (i : Fin n) : LocallyIntegrable (fun x => Du i a x * p i x +
      u i x * naturalCanonicalHessian d g Du x i a) volume := by
    apply locallyIntegrable_iff.mpr
    intro E hE
    exact ((hDu i a E hE).integrable_mul (hp i E hE)).add
      ((hu i E hE).integrable_mul (hC i a E hE))
  have hs := hasLocalWeakCoordinateDerivative_finset_sum Finset.univ
    (fun i _ => hprod i) (fun i _ => hval i) (fun i _ => hder i)
  have hEq : (fun x => ∑ i : Fin n, u i x * p i x) =ᵐ[(volume : Measure (Space n))]
      sourceVectorMass d.potential u := by
    have he := (volume_absolutelyContinuous_potentialMeasure d.source_C1.continuous).ae_eq
      (hessian_mul_naturalCanonicalFlux_ae d g)
    filter_upwards [he] with x hx
    change (∑ i : Fin n, u i x * p i x) = _
    have hp_eq (i : Fin n) : p i x = (coordinateHessian d.potential x *ᵥ (fun i => u i x)) i :=
      (congrFun hx i).symm
    simp_rw [hp_eq]
    simp only [sourceVectorMass, Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  exact hs.congr_ae hEq EventuallyEq.rfl

theorem natural_mass_derivative_covariant_ae (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i a => Du i a x)).IsSymm) :
    ∀ᵐ x ∂potentialMeasure d.potential, ∀ a : Fin n,
      naturalMassRawDerivative d g Du a x =
        2 * (naturalCovariantHessian d g Du x *ᵥ (fun i => naturalCanonicalFlux d g i x)) a := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source, hcomp.filter_mono hac.ae_le,
    sourceThirdAlong_isSymm_ae d (naturalCanonicalFlux d g), hessian_mul_naturalCanonicalFlux_ae d g] with x hH hB hN hp
  intro a
  have he := finite_mass_derivative_eq_covariant (coordinateHessian d.potential x)
    (Matrix.of (fun i a => Du i a x)) (sourceThirdAlong d (naturalCanonicalFlux d g) x)
    hH.1.isHermitian.isSymm hB hN (fun i => naturalCanonicalFlux d g i x) a
  change (∑ i : Fin n, (Du i a x * naturalCanonicalRawGradient d g i x +
    naturalCanonicalFlux d g i x * naturalCanonicalHessian d g Du x i a)) = _
  simp only [Matrix.of_apply] at he
  simpa only [naturalCovariantHessian, naturalCanonicalHessian, hp] using he

end KLSConstantImprovement.ActualNaturalMassWeakDerivative405
#print axioms KLSConstantImprovement.ActualNaturalMassWeakDerivative405.finite_mass_derivative_eq_covariant
#print axioms KLSConstantImprovement.ActualNaturalMassWeakDerivative405.natural_mass_derivative_local_integrable
#print axioms KLSConstantImprovement.ActualNaturalMassWeakDerivative405.natural_mass_hasLocalWeakDerivative
#print axioms KLSConstantImprovement.ActualNaturalMassWeakDerivative405.natural_mass_derivative_covariant_ae

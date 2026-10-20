import KLSConstantImprovement.ActualKatoLocalDomains405
import KLSConstantImprovement.ActualDualBumpDerivative405
import KLSConstantImprovement.ActualLocalDominatedWeakClosure405

/-! The nonlinear scalar chain is obtained from genuine compact joint
chains in (u,p), with a paid local L1 derivative-error bound. In particular
the smooth square-root regularizer of the ACTUAL natural mass is locally
H1 with its literal derivative; no W1,1 renormalization is postulated. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualKatoRegularizedWeakChain405
open KLS ActualBoundedCanonicalSource ActualNaturalDualJoint405 ActualDualBumpControl405
open ActualDualKatoMultiplier405 ActualDualBumpDerivative405 ActualLocalDominatedWeakClosure405
open ActualKatoLocalDomains405 ActualNaturalMassWeakDerivative405 ActualNaturalCovariantEnergy405
open ActualSmoothKatoRegularizer405 ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
open ActualSourceNaturalHessian405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_dual_scalar_weak_chain (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i a E, IsCompact E → MemLp (Du i a) 2 (volume.restrict E))
    (hw : ∀ i a, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i a) a)
    (hC : ∀ i a E, IsCompact E → MemLp (fun x => naturalCanonicalHessian d g Du x i a) 2 (volume.restrict E))
    {F F' : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hderiv : ∀ t, HasDerivAt F (F' t) t)
    (hf : ∀ E, IsCompact E → MemLp
      (fun x => F (sourceVectorMass d.potential (naturalCanonicalFlux d g) x)) 2 (volume.restrict E))
    (hG : ∀ a E, IsCompact E → MemLp
      (fun x => F' (sourceVectorMass d.potential (naturalCanonicalFlux d g) x) * naturalMassRawDerivative d g Du a x)
        2 (volume.restrict E)) (a : Fin n) :
    HasLocalWeakCoordinateDerivative (fun x => F (sourceVectorMass d.potential (naturalCanonicalFlux d g) x))
      (fun x => F' (sourceVectorMass d.potential (naturalCanonicalFlux d g) x) * naturalMassRawDerivative d g Du a x) a := by
  let f (x : Space n) := F (sourceVectorMass d.potential (naturalCanonicalFlux d g) x)
  let G (x : Space n) := F' (sourceVectorMass d.potential (naturalCanonicalFlux d g) x) * naturalMassRawDerivative d g Du a x
  let fk (k : ℕ) := dualSource d g (dualScalarMultiplier F k)
  let Gk (k : ℕ) := dualSourceDerivative d g Du (dualScalarMultiplier F k) a
  have hchain (k : ℕ) := actual_dual_compact_chain d g Du hu hDu hw hC
    (dualScalarMultiplier_contDiff_compact hF k).1 (dualScalarMultiplier_contDiff_compact hF k).2
  obtain ⟨L, hL⟩ := dualBump_uniform_lipschitz (n := n)
  have hvol : (volume : Measure (Space n)) ≪ potentialMeasure d.potential :=
    volume_absolutelyContinuous_potentialMeasure d.source_C1.continuous
  have hmass := (actual_dualMass_eq_ae d g).filter_mono hvol.ae_le
  have hlim : ∀ᵐ x ∂(volume : Measure (Space n)), Tendsto (fun k => fk k x) atTop (𝓝 (f x)) := by
    filter_upwards [hmass] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [actual_dual_bump_eventually d g Du x] with k hk
    change f x = dualBump k (fun b => dualValue d g b x) * F (dualMass (fun b => dualValue d g b x))
    rw [hx, show dualBump k (fun b => dualValue d g b x) = 1 from hk.1, one_mul]
  have hDlim : ∀ᵐ x ∂(volume : Measure (Space n)), Tendsto (fun k => Gk k x) atTop (𝓝 (G x)) := by
    filter_upwards [hmass] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [actual_dual_bump_eventually d g Du x] with k hk
    change G x = fderiv ℝ (dualScalarMultiplier F k) (fun b => dualValue d g b x)
      (fun b => dualDerivative d g Du b a x)
    rw [dualScalarMultiplier_differential hF hderiv, actual_dualMass_derivative, hx,
      show dualBump k (fun b => dualValue d g b x) = 1 from hk.1,
      show fderiv ℝ (dualBump k) (fun b => dualValue d g b x)
        (fun b => dualDerivative d g Du b a x) = 0 from hk.2 a,
      one_mul, mul_zero, add_zero]
  have hdom : ∀ E : Set (Space n), IsCompact E → ∃ b : Space n → ℝ,
      Integrable b (volume.restrict E) ∧ ∀ k, ∀ᵐ x ∂volume.restrict E, ‖fk k x‖ ≤ b x := by
    intro E hE
    letI : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hE.measure_ne_top
    refine ⟨fun x => ‖f x‖, ((hf E hE).integrable (by norm_num)).norm, fun k => ?_⟩
    filter_upwards [ae_restrict_of_ae hmass] with x hx
    change ‖dualBump k (fun b => dualValue d g b x) * F (dualMass (fun b => dualValue d g b x))‖ ≤ ‖f x‖
    rw [hx, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by
      rw [Real.norm_of_nonneg (dualBump_nonnegative_le_one k _).1]
      exact (dualBump_nonnegative_le_one k _).2)
  have hDdom : ∀ E : Set (Space n), IsCompact E → ∃ b : Space n → ℝ,
      Integrable b (volume.restrict E) ∧ ∀ k, ∀ᵐ x ∂volume.restrict E, ‖Gk k x‖ ≤ b x := by
    intro E hE
    letI : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr hE.measure_ne_top
    let B (x : Space n) := (L : ℝ) * dualDerivativeNormSum d g Du a x
    have hB : MemLp B 2 (volume.restrict E) :=
      (dualDerivativeNormSum_local_L2 d g Du hDu hC a E hE).const_mul (L : ℝ)
    have hprod : Integrable (fun x => ‖f x‖ * B x) (volume.restrict E) :=
      (hf E hE).norm.integrable_mul hB
    refine ⟨fun x => ‖G x‖ + ‖f x‖ * B x,
      ((hG a E hE).integrable (by norm_num)).norm.add hprod, fun k => ?_⟩
    have hform := (actual_dual_scalar_multiplier_derivative_ae d g Du hF hderiv k a).filter_mono hvol.ae_le
    filter_upwards [ae_restrict_of_ae hform] with x hx
    have hb : ‖dualSource d g (dualBump k) x‖ ≤ 1 := by
      change ‖dualBump k (fun b => dualValue d g b x)‖ ≤ 1
      rw [Real.norm_of_nonneg (dualBump_nonnegative_le_one k _).1]
      exact (dualBump_nonnegative_le_one k _).2
    have hd : ‖dualSourceDerivative d g Du (dualBump k) a x‖ ≤ B x :=
      dualBump_directional_bound hL k _ _
    change ‖dualSourceDerivative d g Du (dualScalarMultiplier F k) a x‖ ≤ _
    rw [hx, mul_assoc]
    change ‖dualSource d g (dualBump k) x * G x + f x *
      dualSourceDerivative d g Du (dualBump k) a x‖ ≤ _
    calc
      _ ≤ ‖dualSource d g (dualBump k) x * G x‖ +
          ‖f x * dualSourceDerivative d g Du (dualBump k) a x‖ := norm_add_le _ _
      _ ≤ ‖G x‖ + ‖f x‖ * B x := by
        simp only [norm_mul]
        exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) hb)
          (mul_le_mul_of_nonneg_left hd (norm_nonneg _))
  exact local_weak_derivative_of_dominated_limits
    (fun k => locallyIntegrable_of_memLp_two_on_compacts (hchain k).2.1)
    (fun k => locallyIntegrable_of_memLp_two_on_compacts ((hchain k).2.2.1 a))
    (fun k => (hchain k).2.2.2 a) hlim hDlim hdom hDdom

theorem naturalKatoValue_hasLocalWeakDerivative (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i a E, IsCompact E → MemLp (Du i a) 2 (volume.restrict E))
    (hw : ∀ i a, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i a) a)
    (hC : ∀ i a E, IsCompact E → MemLp (fun x => naturalCanonicalHessian d g Du x i a) 2 (volume.restrict E))
    (hcomp : ∀ᵐ x ∂(volume : Measure (Space n)),
      (coordinateHessian d.potential x * Matrix.of (fun i a => Du i a x)).IsSymm)
    (hMi : Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g)) (potentialMeasure d.potential))
    (hEloc : LocallyIntegrable (naturalCovariantEnergy d g Du) volume)
    {ε : ℝ} (hε : 0 < ε) (a : Fin n) :
    HasLocalWeakCoordinateDerivative (naturalKatoValue d g ε) (naturalKatoDerivative d g Du ε a) a :=
  actual_dual_scalar_weak_chain d g Du hu hDu hw hC
    ((katoRegularizer_contDiff hε).of_le (by norm_num)) (katoRegularizer_hasDerivAt hε)
    (naturalKatoValue_local_L2 d g hMi hε)
    (naturalKatoDerivative_local_L2 d g Du hu hDu hC hcomp hMi hEloc hε) a

end KLSConstantImprovement.ActualKatoRegularizedWeakChain405
#print axioms KLSConstantImprovement.ActualKatoRegularizedWeakChain405.actual_dual_scalar_weak_chain
#print axioms KLSConstantImprovement.ActualKatoRegularizedWeakChain405.naturalKatoValue_hasLocalWeakDerivative

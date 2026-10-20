import KLSConstantImprovement.ActualCubicSourceDatum405
import KLSConstantImprovement.ActualSourceNaturalWhitenedHessian405
import KLS.LocalWeakProduct
import KLS.WeakWeightedMean

/-! Genuine global integration by parts between the actual inverse source
gradient and a quadratic monomial. The derivatives are the already paid
weak Hessian, not derivatives of an invented smooth inverse. All global
domains follow from bounded source X/H and the actual L2 inverse gradient.
This discharges the coordinate source-pairing binding used by the cubic
combined energy route; it does not prove the numerical residual90.
-/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualSourceGradientCoordinatePair405
open KLS ActualBoundedCanonicalSource ActualCubicRepresenter
open ActualSourceNaturalTargetCurvatureDomain405 ActualSourceNaturalHessian405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_source_gradient_coordinate_pair (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ)
    (hC : ∀ a b, MemLp (fun x => naturalCanonicalHessian d g Du x a b) 2
      (potentialMeasure d.potential))
    (hw : ∀ a b, HasLocalWeakCoordinateDerivative
      (naturalCanonicalRawGradient d g a)
      (fun x => naturalCanonicalHessian d g Du x a b) b)
    (i j k : Fin n) :
    (∫ x, naturalCanonicalRawGradient d g i x *
      (gradient d.potential x j * gradient d.potential x k - δ j k)
      ∂potentialMeasure d.potential) =
      (∫ x, naturalCanonicalRawGradient d g i x *
        (coordinateHessian d.potential x j k - δ j k)
        ∂potentialMeasure d.potential) +
      ∫ x, gradient d.potential x k * naturalCanonicalHessian d g Du x i j
        ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let p := naturalCanonicalRawGradient d g i
  let X (a : Fin n) (x : Space n) := gradient d.potential x a
  let H (x : Space n) := coordinateHessian d.potential x j k
  let C (x : Space n) := naturalCanonicalHessian d g Du x i j
  have hp : MemLp p 2 (potentialMeasure d.potential) :=
    naturalCanonicalRawGradient_memLp d g i
  have hX (a : Fin n) : MemLp (X a) ∞ (potentialMeasure d.potential) :=
    d.continuous_comp_gradient_memLp (EuclideanSpace.proj a).continuous ∞
  have hH : MemLp H ∞ (potentialMeasure d.potential) := d.hessian_entry_memLp j k ∞
  have hCl : MemLp C 2 (potentialMeasure d.potential) := hC i j
  have hXw : HasLocalWeakCoordinateDerivative (X k) H j := by
    have he : coordinateDerivative d.potential k = X k := by
      funext x
      exact coordinateDerivative_eq_gradient d.potential k x
    have hh := actual_hessian_hasLocalWeakCoordinateDerivative
      d.gradient_lipschitz.locallyLipschitz j k
    rw [he] at hh
    exact hh
  have hXp : HasLocalWeakCoordinateDerivative (fun x => X k x * p x)
      (fun x => H x * p x + X k x * C x) j := by
    apply hXw.mul (hw i j)
    · intro E hE
      exact KLS.MemLp.restrict_volume_of_potentialMeasure
        ((hX k).mono_exponent (by simp)) d.source_C1.continuous hE
    · intro E hE
      exact KLS.MemLp.restrict_volume_of_potentialMeasure hp d.source_C1.continuous hE
    · intro E hE
      exact KLS.MemLp.restrict_volume_of_potentialMeasure
        (hH.mono_exponent (by simp)) d.source_C1.continuous hE
    · intro E hE
      exact KLS.MemLp.restrict_volume_of_potentialMeasure hCl d.source_C1.continuous hE
  have hXp2 : MemLp (fun x => X k x * p x) 2 (potentialMeasure d.potential) :=
    (hX k).mul hp
  have hHp2 : MemLp (fun x => H x * p x) 2 (potentialMeasure d.potential) := hH.mul hp
  have hXC2 : MemLp (fun x => X k x * C x) 2 (potentialMeasure d.potential) :=
    (hX k).mul hCl
  have hXXp2 : MemLp (fun x => (X k x * p x) * X j x) 2
      (potentialMeasure d.potential) := hXp2.mul (hX j)
  have hXpi := hXp2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hHpi := hHp2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hXCi := hXC2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hXXpi := hXXp2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hmean := integral_raw_derivative_potential d.source_C1 hXp hXpi
    (hHpi.add hXCi) (by simpa only [coordinateDerivative_eq_gradient] using hXXpi)
  rw [integral_add hHpi hXCi] at hmean
  have hXXp : Integrable (fun x => p x * (X j x * X k x))
      (potentialMeasure d.potential) := hXXpi.congr (.of_forall fun x => by ring)
  have hpH : Integrable (fun x => p x * H x) (potentialMeasure d.potential) :=
    hHpi.congr (.of_forall fun x => mul_comm _ _)
  have hpδ : Integrable (fun x => p x * δ j k) (potentialMeasure d.potential) :=
    (hp.integrable (by norm_num)).mul_const _
  change (∫ x, p x * (X j x * X k x - δ j k) ∂potentialMeasure d.potential) =
    (∫ x, p x * (H x - δ j k) ∂potentialMeasure d.potential) +
      ∫ x, X k x * C x ∂potentialMeasure d.potential
  simp_rw [mul_sub]
  rw [integral_sub hXXp hpδ, integral_sub hpH hpδ]
  have heXX : (∫ x, (X k x * p x) * coordinateDerivative d.potential j x
      ∂potentialMeasure d.potential) =
      ∫ x, p x * (X j x * X k x) ∂potentialMeasure d.potential := by
    apply integral_congr_ae
    exact .of_forall fun x => by
      dsimp only
      rw [coordinateDerivative_eq_gradient]
      change (X k x * p x) * X j x = _
      ring
  have heH : (∫ x, H x * p x ∂potentialMeasure d.potential) =
      ∫ x, p x * H x ∂potentialMeasure d.potential := by
    apply integral_congr_ae
    exact .of_forall fun x => mul_comm _ _
  rw [heXX, heH] at hmean
  linarith

def actualSourceGradientMainPair (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, T i j k *
    ∫ x, gradient d.potential x k * naturalCanonicalHessian d g Du x i j
      ∂potentialMeasure d.potential

def actualSourceGradientResponse (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) : ℝ :=
  ∑ i, ∑ j, ∑ k, T i j k *
    ∫ x, naturalCanonicalRawGradient d g i x *
      (coordinateHessian d.potential x j k - δ j k)
      ∂potentialMeasure d.potential

/-- The whole literal cubic has the genuine same-source gradient pairing.
The source inverse, its gradient and its Hessian in this statement are
the actual constructed ones. In particular the response is signed. -/
theorem actual_source_gradient_cubic_pair (d : SourceData μ)
    (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k)
    (hT23 : ∀ i j k, T i j k = T i k j)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hC : ∀ a b, MemLp
      (fun x => naturalCanonicalHessian d
        (ActualCubicSourceDatum405.actualCubicDatum d T) Du x a b) 2
      (potentialMeasure d.potential))
    (hw : ∀ a b, HasLocalWeakCoordinateDerivative
      (naturalCanonicalRawGradient d (ActualCubicSourceDatum405.actualCubicDatum d T) a)
      (fun x => naturalCanonicalHessian d
        (ActualCubicSourceDatum405.actualCubicDatum d T) Du x a b) b) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ =
      3 * actualSourceGradientMainPair d T
        (ActualCubicSourceDatum405.actualCubicDatum d T) Du +
      3 * actualSourceGradientResponse d T
        (ActualCubicSourceDatum405.actualCubicDatum d T) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let g := ActualCubicSourceDatum405.actualCubicDatum d T
  let p := naturalCanonicalRawGradient d g
  let X (i : Fin n) (x : Space n) := gradient d.potential x i
  have hp (i : Fin n) : MemLp (p i) 2 (potentialMeasure d.potential) :=
    naturalCanonicalRawGradient_memLp d g i
  have hQ (j k : Fin n) : MemLp
      (fun x => X j x * X k x - δ j k) ∞ (potentialMeasure d.potential) := by
    exact d.continuous_comp_gradient_memLp
      (((EuclideanSpace.proj j).continuous.mul
        (EuclideanSpace.proj k).continuous).sub continuous_const) ∞
  have hi (i j k : Fin n) : Integrable
      (fun x => T i j k * (p i x * (X j x * X k x - δ j k)))
      (potentialMeasure d.potential) := by
    have hm : MemLp (fun x => p i x * (X j x * X k x - δ j k)) 2
        (potentialMeasure d.potential) := (hp i).mul (hQ j k)
    exact (hm.integrable (by norm_num)).const_mul _
  have he (x : Space n) :
      (∑ i, p i x * ActualCubicGradientEnergy.centeredQuadratic (T i) (gradient d.potential x)) =
        ∑ i, ∑ j, ∑ k, T i j k * (p i x * (X j x * X k x - δ j k)) := by
    simp only [ActualCubicGradientEnergy.centeredQuadratic_eq_sum,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    change p i x * (T i j k * (X j x * X k x - δ j k)) = _
    ring
  have hv := ActualCubicSourceDatum405.actual_cubic_self_variational d hμ T hT12 hT23
  change ProbabilityTheory.variance (tensorPolynomial μ T) μ =
    3 * ∫ x, ∑ i, p i x * ActualCubicGradientEnergy.centeredQuadratic (T i)
      (gradient d.potential x) ∂potentialMeasure d.potential at hv
  rw [integral_congr_ae (.of_forall he)] at hv
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ =>
      integrable_finsetSum Finset.univ (fun k _ => hi i j k)))] at hv
  simp_rw [integral_finsetSum Finset.univ (fun j _ =>
    integrable_finsetSum Finset.univ (fun k _ => hi _ j k)),
    integral_finsetSum Finset.univ (fun k _ => hi _ _ k), integral_const_mul] at hv
  have hpairs (i j k : Fin n) :
      (∫ x, p i x * (X j x * X k x - δ j k) ∂potentialMeasure d.potential) =
        (∫ x, p i x * (coordinateHessian d.potential x j k - δ j k)
          ∂potentialMeasure d.potential) +
        ∫ x, gradient d.potential x k * naturalCanonicalHessian d g Du x i j
          ∂potentialMeasure d.potential :=
    actual_source_gradient_coordinate_pair d g Du hC hw i j k
  have hcalc : (∑ i, ∑ j, ∑ k, T i j k *
      ∫ x, p i x * (X j x * X k x - δ j k) ∂potentialMeasure d.potential) =
        actualSourceGradientResponse d T g + actualSourceGradientMainPair d T g Du := by
    simp_rw [hpairs, mul_add, Finset.sum_add_distrib]
    rfl
  change ProbabilityTheory.variance (tensorPolynomial μ T) μ =
    3 * actualSourceGradientMainPair d T g Du + 3 * actualSourceGradientResponse d T g
  linarith

/-- The source-gradient pairing and sub-Bochner domains are supplied on
one actual natural inverse. Matrix Hilbert identification and the numerical
residual payment are separate. Bounded natural mass is the discharged
existential-source gate in the original-law raw405 endpoint. -/
theorem exists_actual_source_gradient_cubic_state_of_mass_bound
    (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k)
    (hT23 : ∀ i j k, T i j k = T i k j)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      ActualSourceLocalizedGaffney405.sourceVectorMass d.potential
        (ActualSourceNaturalGaffney405.naturalCanonicalFlux d
          (ActualCubicSourceDatum405.actualCubicDatum d T)) x ≤ C) :
    ∃ Du : Fin n → Fin n → Space n → ℝ,
      (∀ a b, MemLp
        (fun x => ActualSourceNaturalWhitenedHessian405.naturalWhitenedHessian d
          (ActualCubicSourceDatum405.actualCubicDatum d T) Du x a b) 2
        (potentialMeasure d.potential)) ∧
      (∀ a b, MemLp
        (fun x => naturalCanonicalHessian d
          (ActualCubicSourceDatum405.actualCubicDatum d T) Du x a b) 2
        (potentialMeasure d.potential)) ∧
      (∀ a b, HasLocalWeakCoordinateDerivative
        (naturalCanonicalRawGradient d (ActualCubicSourceDatum405.actualCubicDatum d T) a)
        (fun x => naturalCanonicalHessian d
          (ActualCubicSourceDatum405.actualCubicDatum d T) Du x a b) b) ∧
      ProbabilityTheory.variance (tensorPolynomial μ T) μ =
        3 * actualSourceGradientMainPair d T
          (ActualCubicSourceDatum405.actualCubicDatum d T) Du +
        3 * actualSourceGradientResponse d T
          (ActualCubicSourceDatum405.actualCubicDatum d T) ∧
      (∫ x, KLS.matrixFrobeniusSq
        (ActualSourceNaturalWhitenedHessian405.naturalWhitenedHessian d
          (ActualCubicSourceDatum405.actualCubicDatum d T) Du x) +
        ActualSourceConnectionFields405.sourceConnectionTarget d
          (ActualSourceNaturalGaffney405.naturalCanonicalFlux d
            (ActualCubicSourceDatum405.actualCubicDatum d T)) x
          ∂potentialMeasure d.potential) ≤
        ProbabilityTheory.variance (tensorPolynomial μ T) μ := by
  let g := ActualCubicSourceDatum405.actualCubicDatum d T
  obtain ⟨Du, _, _, _, hCloc, hw, hCsym, hEi, _, _, hb⟩ :=
    ActualSourceBoundedMassBochner405.exists_naturalCanonicalHessian_bochner_of_mass_bound
      d hn g (ActualCubicSourceDatum405.actualCubicDatum_mean_zero d hμ T) hC hM
  have hW := ActualSourceNaturalWhitenedHessian405.naturalWhitenedHessian_entry_memLp
    d g Du hCloc hCsym hEi
  have hCl2 := ActualSourceNaturalWhitenedHessian405.naturalCanonicalHessian_entry_memLp
    d g Du hCloc hCsym hEi
  refine ⟨Du, hW, hCl2, hw,
    actual_source_gradient_cubic_pair d hμ T hT12 hT23 Du hCl2 hw, ?_⟩
  have he := ActualSourceNaturalWhitenedHessian405.naturalWhitenedHessian_square_eq_energy_ae
    d g Du hCsym
  calc
    _ = ∫ x, naturalCanonicalHessianEnergy d g Du x +
        ActualSourceConnectionFields405.sourceConnectionTarget d
          (ActualSourceNaturalGaffney405.naturalCanonicalFlux d g) x
          ∂potentialMeasure d.potential :=
      integral_congr_ae (he.fun_add EventuallyEq.rfl)
    _ ≤ ‖g‖ ^ 2 := hb
    _ = _ := ActualCubicSourceDatum405.actualCubicDatum_norm_sq d hμ T

end KLSConstantImprovement.ActualSourceGradientCoordinatePair405
#print axioms KLSConstantImprovement.ActualSourceGradientCoordinatePair405.actual_source_gradient_coordinate_pair
#print axioms KLSConstantImprovement.ActualSourceGradientCoordinatePair405.actual_source_gradient_cubic_pair
#print axioms KLSConstantImprovement.ActualSourceGradientCoordinatePair405.exists_actual_source_gradient_cubic_state_of_mass_bound

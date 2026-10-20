import KLSConstantImprovement.ActualAffineResponseHilbert405
import KLSConstantImprovement.ActualAffineTraceDiscount405
import KLSConstantImprovement.ActualDirectDiskBudget405
import KLSConstantImprovement.ActualSourceDirectCubicCharge405
import KLSConstantImprovement.SourceProductionJointRaw405Payoff
import KLSConstantImprovement.SourceGradientCubicSubBochner

/-! Same actual cubic inverse and the actual affine/response matrix fields.
The affine main cost is exactly the norm of b in this construction.
Its already paid disk bound weakens the sufficient residual90 gate to
residual178. No numerical residual estimate is asserted here.
-/
noncomputable section
open MeasureTheory Matrix Filter ProbabilityTheory
open scoped BigOperators
namespace KLSConstantImprovement.ActualSourceGradientCombinedEnergy405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualCubicRepresenter ActualCubicSourceDatum405 ActualNaturalGradientForm405
open ActualSourceQuadraticEta405 ActualCubicRowVariational405 ActualCubicMatrixFactorization405
open ActualSourceNaturalTargetCurvatureDomain405 ActualSourceNaturalWhitenedHessian405
open ActualSourceNaturalGaffney405 ActualSourceNaturalHessian405 ActualSourceLocalizedGaffney405
open ActualSourceBoundedMassBochner405 ActualSourceConnectionFields405
open ActualQuadraticHilbertMatrix405 ActualAffineResponseHilbert405
open ActualAffineMatrixTests405 ActualAffineGlobalBalance405 ActualAffineTraceDiscount405
open ActualDirectDiskBudget405 ActualSourceDirectCubicBalance405 ActualSourceDirectCubicCharge405
open ActualDirectCubicPointwise405 SourceProductionJointRaw405Payoff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_affine_main_cost_le_seventeen_half (d : SourceData μ)
    (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j) :
    (∫ x, actualAffineMainCost d T x ∂potentialMeasure d.potential) ≤
      (35 / 2 : ℝ) * (ActualDeficitTensorBounds.tensorSquare T - actualOrientationGap d T / 2) -
        (7 / 10 : ℝ) * actualAffineDiscount d T := by
  have hq := actual_affine_discount_bounds d T h12 h23
  have hj := rational_affine_main_discount (hq.1.trans hq.2) hq.1
    (actual_affine_main_discount d T h12 h23)
  have hd := actual_direct_universal_constant d hμ.isotropic T h12 h23
  have hp := actual_direct_target_curvature_nonnegative d T
    (fun i => Matrix.IsSymm.ext fun a b => h23 i b a)
  have hc := actual_direct_commutator_integral_nonnegative d T
  obtain ⟨_, _, _, _, hN⟩ := actual_disk_nonnegative_and_budget d hμ.isotropic T h12 h23
  have hs : Real.sqrt (2 : ℝ) ≤ 99 / 70 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  have hmul := mul_nonneg hN (sub_nonneg.mpr hs)
  have hW : (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) ≤
      (507 / 70 : ℝ) *
        (ActualDeficitTensorBounds.tensorSquare T - actualOrientationGap d T / 2) := by
    nlinarith
  nlinarith

def actualSourceGradientCurvature (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∫ x, sourceConnectionTarget d (naturalCanonicalFlux d (actualCubicDatum d T)) x
    ∂potentialMeasure d.potential

def actualSourceGradientResidual (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hW : ∀ i j, MemLp
      (fun x => naturalWhitenedHessian d (actualCubicDatum d T) Du x i j) 2
      (potentialMeasure d.potential)) : ℝ :=
  6 * inner ℝ (naturalWhiteHilbert d (actualCubicDatum d T) Du hW)
      (actualResponseHilbert d T) -
    ‖naturalWhiteHilbert d (actualCubicDatum d T) Du hW -
      (3 : ℝ) • actualAffineHilbert d T‖ ^ 2 - actualSourceGradientCurvature d T

/-- Fixed-Du actual cubic factorization. This selects coordinate form
elements from the same actual natural Hessian used in Bochner. -/
theorem actual_cubic_fixed_hessian_factorization (d : SourceData μ)
    (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hW : ∀ a b, MemLp (fun x => naturalWhitenedHessian d
      (actualCubicDatum d T) Du x a b) 2 (potentialMeasure d.potential))
    (hC : ∀ a b, MemLp (fun x => naturalCanonicalHessian d
      (actualCubicDatum d T) Du x a b) 2 (potentialMeasure d.potential))
    (hw : ∀ a b, HasLocalWeakCoordinateDerivative
      (naturalCanonicalRawGradient d (actualCubicDatum d T) a)
      (fun x => naturalCanonicalHessian d (actualCubicDatum d T) Du x a b) b) :
    variance (tensorPolynomial μ T) μ =
      6 * inner ℝ (actualQuadraticHilbert d T)
        (naturalWhiteHilbert d (actualCubicDatum d T) Du hW) := by
  let g := actualCubicDatum d T
  choose U hU using fun i => exists_natural_gradient_coordinate_form d g Du hW hC hw i
  have he (i : Fin n) := actual_quadratic_eta_gradient_test d hμ (T i) g i (U i) (hU i).1
  have hi (i : Fin n) : Integrable (fun x => naturalCanonicalRawGradient d g i x *
      ActualCubicGradientEnergy.centeredQuadratic (T i) (gradient d.potential x))
      (potentialMeasure d.potential) :=
    (naturalCanonicalRawGradient_memLp d g i).integrable_mul
      (d.continuous_comp_gradient_memLp
        ((contDiff_matrixQuadratic (T i)).sub contDiff_const).continuous 2)
  have hv := actual_cubic_self_variational d hμ T h12 h23
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)] at hv
  have hsum : (∑ i, canonicalMetricEnergy d.potential (quadraticSourceEta d (T i)) (U i)) =
      (1 / 2 : ℝ) * ∑ i, ∫ x, naturalCanonicalRawGradient d g i x *
        ActualCubicGradientEnergy.centeredQuadratic (T i) (gradient d.potential x)
        ∂potentialMeasure d.potential := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => he i
  have hf := actual_row_energy_white_pairing d T g Du hW U (fun i r => (hU i).2 r)
  rw [hf] at hsum
  change variance (tensorPolynomial μ T) μ =
    3 * ∑ i, ∫ x, naturalCanonicalRawGradient d g i x *
      ActualCubicGradientEnergy.centeredQuadratic (T i) (gradient d.potential x)
      ∂potentialMeasure d.potential at hv
  linarith

/-- One actual Du pays both the source cubic pairing and the target
curvature sub-Bochner bound; no free pair/Bochner witness is supplied. -/
theorem exists_actual_source_gradient_residual_bound_of_mass_bound
    (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (actualCubicDatum d T)) x ≤ C) :
    ∃ (Du : Fin n → Fin n → Space n → ℝ)
      (hW : ∀ a b, MemLp (fun x => naturalWhitenedHessian d
        (actualCubicDatum d T) Du x a b) 2 (potentialMeasure d.potential)),
      variance (tensorPolynomial μ T) μ -
        9 * (∫ x, actualAffineMainCost d T x ∂potentialMeasure d.potential) ≤
          actualSourceGradientResidual d T Du hW := by
  let g := actualCubicDatum d T
  obtain ⟨Du, _, _, _, hCloc, hw, hCsym, hEi, _, hPi, hb⟩ :=
    exists_naturalCanonicalHessian_bochner_of_mass_bound d hn g
      (actualCubicDatum_mean_zero d hμ T) hC hM
  have hW := naturalWhitenedHessian_entry_memLp d g Du hCloc hCsym hEi
  have hCl2 := naturalCanonicalHessian_entry_memLp d g Du hCloc hCsym hEi
  let r := naturalWhiteHilbert d g Du hW
  let b := actualAffineHilbert d T
  let F := actualResponseHilbert d T
  have hv := actual_cubic_fixed_hessian_factorization d hμ T h12 h23 Du hW hCl2 hw
  have hsplit := actual_affine_response_hilbert_split d T
  have hinner := congrArg (fun z => inner ℝ z r) hsplit
  rw [inner_add_left, real_inner_smul_left] at hinner
  have hpair : variance (tensorPolynomial μ T) μ =
      3 * inner ℝ r b + 3 * inner ℝ r F := by
    have hbcomm : inner ℝ r b = inner ℝ b r := (real_inner_comm r b).symm
    have hfcomm : inner ℝ r F = inner ℝ F r := (real_inner_comm r F).symm
    change variance (tensorPolynomial μ T) μ =
      3 * inner ℝ r b + 3 * inner ℝ r F
    linarith
  have hbochner : ‖r‖ ^ 2 + actualSourceGradientCurvature d T ≤
      variance (tensorPolynomial μ T) μ := by
    rw [naturalWhiteHilbert_norm]
    dsimp only [actualSourceGradientCurvature]
    rw [integral_congr_ae (naturalWhitenedHessian_square_eq_energy_ae d g Du hCsym)]
    rw [← integral_add hEi hPi]
    exact hb.trans_eq (actualCubicDatum_norm_sq d hμ T)
  have h := SourceGradientCubicSubBochner.source_gradient_variance_upper b r hpair hbochner
  refine ⟨Du, hW, ?_⟩
  rw [actualAffineHilbert_norm d T (fun i => Matrix.IsSymm.ext fun a b => h23 i b a)] at h
  exact h

/-- A concrete sufficient gate on the actual residual. The bound178 is
an explicit OPEN premise; this theorem does not assert it universally. -/
theorem actual_residual178_gives_cubic335_half (d : SourceData μ)
    (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hW : ∀ a b, MemLp (fun x => naturalWhitenedHessian d
      (actualCubicDatum d T) Du x a b) 2 (potentialMeasure d.potential))
    (hactual : variance (tensorPolynomial μ T) μ -
      9 * (∫ x, actualAffineMainCost d T x ∂potentialMeasure d.potential) ≤
        actualSourceGradientResidual d T Du hW)
    (hresidual : actualSourceGradientResidual d T Du hW ≤
      178 * ActualDeficitTensorBounds.tensorSquare T) :
    variance (tensorPolynomial μ T) μ ≤
      (671 / 2 : ℝ) * ActualDeficitTensorBounds.tensorSquare T -
        (315 / 4 : ℝ) * actualOrientationGap d T -
          (63 / 10 : ℝ) * actualAffineDiscount d T := by
  have hJ := actual_affine_main_cost_le_seventeen_half d hμ T h12 h23
  linarith

end KLSConstantImprovement.ActualSourceGradientCombinedEnergy405
#print axioms KLSConstantImprovement.ActualSourceGradientCombinedEnergy405.actual_affine_main_cost_le_seventeen_half
#print axioms KLSConstantImprovement.ActualSourceGradientCombinedEnergy405.actual_cubic_fixed_hessian_factorization
#print axioms KLSConstantImprovement.ActualSourceGradientCombinedEnergy405.exists_actual_source_gradient_residual_bound_of_mass_bound
#print axioms KLSConstantImprovement.ActualSourceGradientCombinedEnergy405.actual_residual178_gives_cubic335_half

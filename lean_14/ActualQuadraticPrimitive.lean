import ActualGradedTensorOperators
import QuadraticAppellBridge

/-! The actual inverse-gradient operator integrates a linear matrix field
to the centered quadratic Appell polynomial. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix Set Filter
open scoped ContDiff BigOperators RealInnerProductSpace ENNReal
namespace KLS.DeterministicBridgeIntegration
open KLS.DeterministicBridge
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]

theorem exists_weightedH1_quadraticAppell
    (hφ : Continuous φ) (hμ : admissibleMeasure (potentialMeasure φ))
    (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.IsSymm) :
    ∃ U : WeightedCenteredH1 φ,
      (weightedH1Value φ U : Space n → ℝ) =ᵐ[potentialMeasure φ]
        quadraticAppellPrimitive (potentialMeasure φ) T ∧
      ∀ i, (weightedH1Derivative φ i U : Space n → ℝ) =ᵐ[potentialMeasure φ]
        fun x => matrixAction T x i := by
  have hq := quadraticAppellPrimitive_memLp hμ.quadraticVarianceEight_unconditional.memLp_coordinate_mul T
  have hdiff : ContDiff ℝ (⊤ : ℕ∞) (quadraticAppellPrimitive (potentialMeasure φ) T) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => (1/2 : ℝ) •
      (matrixQuadratic T x-∫ y, matrixQuadratic T y ∂potentialMeasure φ))
    exact (((contDiff_matrixQuadratic T).sub contDiff_const).const_smul (1/2 : ℝ)).of_le (by simp)
  have hd (i : Fin n) :
      MemLp (coordinateDerivative (quadraticAppellPrimitive (potentialMeasure φ) T) i)
        2 (potentialMeasure φ) := by
    have he : coordinateDerivative (quadraticAppellPrimitive (potentialMeasure φ) T) i =
        fun x => ∑ j, T i j*x j := by
      funext x
      rw [coordinateDerivative_eq_gradient,quadraticAppellPrimitive_gradient _ _ hT,
        matrixAction_apply]
    rw [he]
    exact memLp_finsetSum _ (fun j _ => (hμ.isotropic.memLp_coordinate j).const_mul (T i j))
  obtain ⟨U,hv,hD⟩ := exists_weightedH1_of_faithful_test hφ
    ⟨(hdiff.of_le (by simp)).locallyLipschitz,hq⟩
      (energy_lt_top_of_memLp_coordinateDerivative hd)
  refine ⟨U,?_,fun i => ?_⟩
  · simpa only [quadraticAppellPrimitive_integral_eq_zero
      hμ.quadraticVarianceEight_unconditional.memLp_coordinate_mul T,sub_zero] using hv
  · filter_upwards [hD i] with x hx
    rw [hx,coordinateDerivative_eq_gradient,quadraticAppellPrimitive_gradient _ _ hT]

theorem weightedGradientPrimitive_quadratic_value_ae
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hμ : admissibleMeasure (potentialMeasure φ))
    (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.IsSymm)
    (G : VectorField (φ := φ))
    (hG : ∀ i, (G i : Space n → ℝ) =ᵐ[potentialMeasure φ] fun x => matrixAction T x i) :
    (weightedH1Value φ (weightedGradientPrimitive hφ hκ hlower G) : Space n → ℝ)
      =ᵐ[potentialMeasure φ] quadraticAppellPrimitive (potentialMeasure φ) T := by
  obtain ⟨U,hv,hD⟩ := exists_weightedH1_quadraticAppell hφ.continuous hμ T hT
  have he : weightedH1Gradient φ U=G := by
    apply PiLp.ext
    intro i
    exact Lp.ext ((hD i).trans (hG i).symm)
  rw [←he,weightedGradientPrimitive_gradient]
  exact hv

theorem weightedGradientPrimitive_quadratic_norm_sq_le_two
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hμ : admissibleMeasure (potentialMeasure φ))
    (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.IsSymm)
    (G : VectorField (φ := φ))
    (hG : ∀ i, (G i : Space n → ℝ) =ᵐ[potentialMeasure φ] fun x => matrixAction T x i) :
    ‖weightedH1Value φ (weightedGradientPrimitive hφ hκ hlower G)‖^2 ≤
      2*matrixFrobeniusSq T := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  calc
    _ = ∫ x, quadraticAppellPrimitive (potentialMeasure φ) T x^2 ∂potentialMeasure φ := by
      apply integral_congr_ae
      filter_upwards [weightedGradientPrimitive_quadratic_value_ae hφ hκ hlower hμ T hT G hG]
        with x hx
      simp only [hx,RCLike.inner_apply,conj_trivial,pow_two]
    _ ≤ _ := quadraticAppellPrimitive_integral_sq_le_two hμ T hT

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.weightedGradientPrimitive_quadratic_value_ae
#print axioms KLS.DeterministicBridgeIntegration.weightedGradientPrimitive_quadratic_norm_sq_le_two

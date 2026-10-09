import KLS.WeightedCenteredGradientInverse
import KLS.WeightedEnergyGraphClosability

/-! A genuine weighted gradient-range inverse and orthogonal projection.
The coercivity input is the actual positive Hessian lower bound, already
proved sufficient in the release. No dimension-free numerical gap, Hodge
estimate, or identification of every curl-free field with a gradient is
assumed. The last identification remains an analytic obligation. -/

open MeasureTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff RealInnerProductSpace BigOperators

noncomputable section
namespace KLS.DeterministicBridgeIntegration
variable {n : ℕ}

theorem weightedEnergyForm_eq_gradient_inner (φ : Space n → ℝ)
    (U V : WeightedCenteredH1 φ) :
    weightedEnergyForm φ U V =
      inner ℝ (weightedH1Gradient φ U) (weightedH1Gradient φ V) := by
  simp only [weightedEnergyForm_apply, PiLp.inner_apply, weightedH1Gradient_apply]

/-- The actual vector-field forcing uses the adjoint of the genuine weak
gradient. This is different from the old scalar Poisson forcing. -/
def weightedGradientPrimitive {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a)) :
    CenteredL2.Family (potentialMeasure φ) (Fin n) →L[ℝ] WeightedCenteredH1 φ :=
  (weightedEnergyForm_isCoercive hφ hκ hlower).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (weightedH1Gradient φ).adjoint

section ActualPotential
variable {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ),
    κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

theorem weightedGradientPrimitive_variational
    (F : CenteredL2.Family (potentialMeasure φ) (Fin n))
    (V : WeightedCenteredH1 φ) :
    weightedEnergyForm φ (weightedGradientPrimitive hφ hκ hlower F) V =
      inner ℝ F (weightedH1Gradient φ V) := by
  let hc := weightedEnergyForm_isCoercive hφ hκ hlower
  rw [← hc.continuousLinearEquivOfBilin_apply]
  change inner ℝ (hc.continuousLinearEquivOfBilin
    (hc.continuousLinearEquivOfBilin.symm ((weightedH1Gradient φ).adjoint F))) V = _
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.adjoint_inner_left]

theorem weightedGradientPrimitive_unique
    (F : CenteredL2.Family (potentialMeasure φ) (Fin n))
    {U : WeightedCenteredH1 φ}
    (hU : ∀ V, weightedEnergyForm φ U V = inner ℝ F (weightedH1Gradient φ V)) :
    U = weightedGradientPrimitive hφ hκ hlower F := by
  let hc := weightedEnergyForm_isCoercive hφ hκ hlower
  have he : (weightedH1Gradient φ).adjoint F = hc.continuousLinearEquivOfBilin U := by
    apply hc.unique_continuousLinearEquivOfBilin
    intro V
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact (hU V).symm
  calc
    U = hc.continuousLinearEquivOfBilin.symm (hc.continuousLinearEquivOfBilin U) :=
      (hc.continuousLinearEquivOfBilin.symm_apply_apply U).symm
    _ = hc.continuousLinearEquivOfBilin.symm ((weightedH1Gradient φ).adjoint F) := by rw [he]
    _ = weightedGradientPrimitive hφ hκ hlower F := rfl

/-- Taking a genuine gradient and then the centered primitive recovers the
original graph element, including its actual L2 value and all derivatives. -/
theorem weightedGradientPrimitive_gradient (U : WeightedCenteredH1 φ) :
    weightedGradientPrimitive hφ hκ hlower (weightedH1Gradient φ U) = U := by
  symm
  apply weightedGradientPrimitive_unique hφ hκ hlower
  intro V
  exact weightedEnergyForm_eq_gradient_inner φ U V

/-- The solution gradient is contractive on every actual vector L2 forcing. -/
theorem weightedGradientPrimitive_gradient_norm_le
    (F : CenteredL2.Family (potentialMeasure φ) (Fin n)) :
    ‖weightedH1Gradient φ (weightedGradientPrimitive hφ hκ hlower F)‖ ≤ ‖F‖ := by
  let U := weightedGradientPrimitive hφ hκ hlower F
  have he := weightedGradientPrimitive_variational hφ hκ hlower F U
  rw [weightedEnergyForm_eq_gradient_inner, real_inner_self_eq_norm_sq] at he
  have hi := real_inner_le_norm F (weightedH1Gradient φ U)
  change ‖weightedH1Gradient φ U‖ ≤ ‖F‖
  nlinarith [norm_nonneg (weightedH1Gradient φ U), norm_nonneg F]

/-- Orthogonal projection onto the actual range of the closed weak gradient. -/
def weightedGradientProjection :
    CenteredL2.Family (potentialMeasure φ) (Fin n) →L[ℝ]
      CenteredL2.Family (potentialMeasure φ) (Fin n) :=
  (weightedH1Gradient φ).comp (weightedGradientPrimitive hφ hκ hlower)

theorem weightedGradientProjection_gradient (U : WeightedCenteredH1 φ) :
    weightedGradientProjection hφ hκ hlower (weightedH1Gradient φ U) =
      weightedH1Gradient φ U := by
  simp only [weightedGradientProjection, ContinuousLinearMap.comp_apply,
    weightedGradientPrimitive_gradient]

theorem weightedGradientProjection_idempotent
    (F : CenteredL2.Family (potentialMeasure φ) (Fin n)) :
    weightedGradientProjection hφ hκ hlower
      (weightedGradientProjection hφ hκ hlower F) =
        weightedGradientProjection hφ hκ hlower F := by
  exact weightedGradientProjection_gradient hφ hκ hlower _

theorem weightedGradientProjection_norm_le
    (F : CenteredL2.Family (potentialMeasure φ) (Fin n)) :
    ‖weightedGradientProjection hφ hκ hlower F‖ ≤ ‖F‖ :=
  weightedGradientPrimitive_gradient_norm_le hφ hκ hlower F

theorem weightedGradientProjection_residual_orthogonal
    (F : CenteredL2.Family (potentialMeasure φ) (Fin n))
    (U : WeightedCenteredH1 φ) :
    inner ℝ (F - weightedGradientProjection hφ hκ hlower F)
      (weightedH1Gradient φ U) = 0 := by
  rw [inner_sub_left]
  have he := weightedGradientPrimitive_variational hφ hκ hlower F U
  rw [weightedEnergyForm_eq_gradient_inner] at he
  change inner ℝ F (weightedH1Gradient φ U) -
    inner ℝ (weightedH1Gradient φ (weightedGradientPrimitive hφ hκ hlower F))
      (weightedH1Gradient φ U) = 0
  linarith

theorem weightedGradientProjection_selfAdjoint
    (F G : CenteredL2.Family (potentialMeasure φ) (Fin n)) :
    inner ℝ (weightedGradientProjection hφ hκ hlower F) G =
      inner ℝ F (weightedGradientProjection hφ hκ hlower G) := by
  have hF := weightedGradientProjection_residual_orthogonal hφ hκ hlower F
    (weightedGradientPrimitive hφ hκ hlower G)
  have hG := weightedGradientProjection_residual_orthogonal hφ hκ hlower G
    (weightedGradientPrimitive hφ hκ hlower F)
  change inner ℝ (F - weightedGradientProjection hφ hκ hlower F)
    (weightedGradientProjection hφ hκ hlower G) = 0 at hF
  change inner ℝ (G - weightedGradientProjection hφ hκ hlower G)
    (weightedGradientProjection hφ hκ hlower F) = 0 at hG
  rw [inner_sub_left] at hF hG
  have hc1 : inner ℝ G (weightedGradientProjection hφ hκ hlower F) =
      inner ℝ (weightedGradientProjection hφ hκ hlower F) G := real_inner_comm _ _
  have hc2 : inner ℝ (weightedGradientProjection hφ hκ hlower G)
      (weightedGradientProjection hφ hκ hlower F) =
      inner ℝ (weightedGradientProjection hφ hκ hlower F)
        (weightedGradientProjection hφ hκ hlower G) := real_inner_comm _ _
  rw [hc1, hc2] at hG
  linarith

/-- The actual gradient range is closed, because it is exactly the fixed
space of the bounded orthogonal projection just constructed. -/
theorem weightedGradientRange_eq_ker :
    LinearMap.range (weightedH1Gradient φ).toLinearMap =
      LinearMap.ker
        (weightedGradientProjection hφ hκ hlower -
          ContinuousLinearMap.id ℝ
            (CenteredL2.Family (potentialMeasure φ) (Fin n))).toLinearMap := by
  ext F
  constructor
  · rintro ⟨U, rfl⟩
    change weightedGradientProjection hφ hκ hlower (weightedH1Gradient φ U) -
      weightedH1Gradient φ U = 0
    rw [weightedGradientProjection_gradient, sub_self]
  · intro hF
    change weightedGradientProjection hφ hκ hlower F - F = 0 at hF
    exact ⟨weightedGradientPrimitive hφ hκ hlower F, sub_eq_zero.mp hF⟩

include hφ hκ hlower in
theorem weightedGradientRange_isClosed :
    IsClosed (LinearMap.range (weightedH1Gradient φ).toLinearMap :
      Set (CenteredL2.Family (potentialMeasure φ) (Fin n))) := by
  rw [weightedGradientRange_eq_ker hφ hκ hlower]
  exact (weightedGradientProjection hφ hκ hlower -
    ContinuousLinearMap.id ℝ _).isClosed_ker

/-- The actual centered value of the vector-forced primitive is bounded,
using only the proved measure-dependent Hessian lower bound. -/
theorem weightedGradientPrimitive_value_norm_le
    (F : CenteredL2.Family (potentialMeasure φ) (Fin n)) :
    ‖weightedH1Value φ (weightedGradientPrimitive hφ hκ hlower F)‖ ≤
      Real.sqrt κ⁻¹ * ‖F‖ := by
  let U := weightedGradientPrimitive hφ hκ hlower F
  have hP := weightedH1_value_norm_sq_le_energy hφ hκ hlower U
  rw [← weightedH1Gradient_norm_sq] at hP
  have hG := weightedGradientPrimitive_gradient_norm_le hφ hκ hlower F
  have hsq := Real.sq_sqrt (inv_nonneg.mpr hκ.le)
  have hGs : ‖weightedH1Gradient φ U‖ ^ 2 ≤ ‖F‖ ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hG
  have hm := mul_le_mul_of_nonneg_left hGs (inv_nonneg.mpr hκ.le)
  change ‖weightedH1Value φ U‖ ≤ Real.sqrt κ⁻¹ * ‖F‖
  nlinarith [norm_nonneg (weightedH1Value φ U),
    mul_nonneg (Real.sqrt_nonneg κ⁻¹) (norm_nonneg F)]

theorem weightedGradientPrimitive_integral_eq_zero
    (F : CenteredL2.Family (potentialMeasure φ) (Fin n)) :
    (∫ x, weightedH1Value φ (weightedGradientPrimitive hφ hκ hlower F) x
      ∂potentialMeasure φ) = 0 :=
  weightedH1_integral_eq_zero hφ.continuous _

include hφ hκ hlower in
/-- Every vector field in the actual gradient range has exactly one centered
graph primitive. The displayed candidate is constructed by the old proved
coercive form, rather than by an existence hypothesis. -/
theorem existsUnique_weightedGradientPrimitive_of_mem_range
    (F : CenteredL2.Family (potentialMeasure φ) (Fin n))
    (hF : F ∈ LinearMap.range (weightedH1Gradient φ).toLinearMap) :
    ∃! U : WeightedCenteredH1 φ, weightedH1Gradient φ U = F := by
  obtain ⟨V, rfl⟩ := hF
  refine ⟨V, rfl, ?_⟩
  intro U hU
  have he := congrArg (weightedGradientPrimitive hφ hκ hlower) hU
  change weightedGradientPrimitive hφ hκ hlower (weightedH1Gradient φ U) =
    weightedGradientPrimitive hφ hκ hlower (weightedH1Gradient φ V) at he
  simpa only [weightedGradientPrimitive_gradient] using he

theorem weightedGradientPrimitive_value_norm_le_of_rayleigh
    {lam : ℝ} (hlam : 0 < lam)
    (hRay : ∀ U : WeightedCenteredH1 φ,
      lam * ‖weightedH1Value φ U‖ ^ 2 ≤ weightedEnergyForm φ U U)
    (F : CenteredL2.Family (potentialMeasure φ) (Fin n)) :
    ‖weightedH1Value φ (weightedGradientPrimitive hφ hκ hlower F)‖ ≤
      Real.sqrt lam⁻¹ * ‖F‖ := by
  let U := weightedGradientPrimitive hφ hκ hlower F
  have hP := hRay U
  rw [weightedEnergyForm_eq_gradient_inner, real_inner_self_eq_norm_sq] at hP
  have hG := weightedGradientPrimitive_gradient_norm_le hφ hκ hlower F
  have hGs : ‖weightedH1Gradient φ U‖ ^ 2 ≤ ‖F‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hG
  have hb : ‖weightedH1Value φ U‖ ^ 2 ≤ lam⁻¹ * ‖F‖ ^ 2 := by
    apply (le_inv_mul_iff₀ hlam).mpr
    exact hP.trans hGs
  have hsq := Real.sq_sqrt (inv_nonneg.mpr hlam.le)
  change ‖weightedH1Value φ U‖ ≤ Real.sqrt lam⁻¹ * ‖F‖
  nlinarith [norm_nonneg (weightedH1Value φ U),
    mul_nonneg (Real.sqrt_nonneg lam⁻¹) (norm_nonneg F)]

/-- The actual optimal constant controls this primitive on every vector
forcing. The eigenvalue is supplied by the released attainment theorem;
there is no assumed universal numerical spectral gap. -/
theorem exists_optimal_weightedGradientPrimitive_bound (hn : 0 < n) :
    ∃ lam : ℝ, 0 < lam ∧
      poincareConstant (potentialMeasure φ) = ENNReal.ofReal lam⁻¹ ∧
      ∀ F : CenteredL2.Family (potentialMeasure φ) (Fin n),
        ‖weightedH1Value φ (weightedGradientPrimitive hφ hκ hlower F)‖ ≤
          Real.sqrt lam⁻¹ * ‖F‖ := by
  obtain ⟨lam, U, _, hlam, hU, hweak, hmin, hCP⟩ :=
    exists_positive_weighted_eigenpair_with_optimal_poincare hn hφ hκ hlower
  have he : weightedEnergyForm φ U U = lam := by
    simpa only [real_inner_self_eq_norm_sq, hU, one_pow, mul_one] using hweak U
  have hm : ∀ V : WeightedCenteredH1 φ, ‖weightedH1Value φ V‖ = 1 →
      weightedEnergyForm φ U U ≤ weightedEnergyForm φ V V := by rwa [he]
  have hRay (V : WeightedCenteredH1 φ) :
      lam * ‖weightedH1Value φ V‖ ^ 2 ≤ weightedEnergyForm φ V V := by
    simpa only [he] using weightedRayleigh_minimizer_lower_bound hm V
  exact ⟨lam, hlam, hCP,
    weightedGradientPrimitive_value_norm_le_of_rayleigh hφ hκ hlower hlam hRay⟩

end ActualPotential

/-- Every actual weighted graph gradient is curl-free in the ordinary
distributional sense. Only the compact test is differentiated twice. -/
theorem weightedH1Gradient_distributionally_curlFree
    {φ : Space n → ℝ} (hφ : ContDiff ℝ 1 φ)
    (U : WeightedCenteredH1 φ) (i j : Fin n)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
    (∫ x, weightedH1Gradient φ U i x * coordinateDerivative ψ j x) =
      ∫ x, weightedH1Gradient φ U j x * coordinateDerivative ψ i x := by
  have hd (k : Fin n) : ContDiff ℝ 1 (coordinateDerivative ψ k) :=
    contDiff_coordinateDerivative hψ (by simp) k
  have he : coordinateDerivative (coordinateDerivative ψ j) i =
      coordinateDerivative (coordinateDerivative ψ i) j := by
    funext x
    exact (coordinateHessian_symmetric (hψ.of_le (by simp)) x).apply j i
  have hi := weightedH1_unweighted_weak_identity hφ U (hd j)
    (hasCompactSupport_coordinateDerivative hc j) i
  have hj := weightedH1_unweighted_weak_identity hφ U (hd i)
    (hasCompactSupport_coordinateDerivative hc i) j
  rw [he] at hi
  simp only [weightedH1Gradient_apply]
  linarith

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.weightedGradientPrimitive_gradient
#print axioms KLS.DeterministicBridgeIntegration.weightedGradientProjection_selfAdjoint
#print axioms KLS.DeterministicBridgeIntegration.weightedGradientRange_isClosed
#print axioms KLS.DeterministicBridgeIntegration.weightedGradientPrimitive_value_norm_le
#print axioms KLS.DeterministicBridgeIntegration.existsUnique_weightedGradientPrimitive_of_mem_range
#print axioms KLS.DeterministicBridgeIntegration.exists_optimal_weightedGradientPrimitive_bound
#print axioms KLS.DeterministicBridgeIntegration.weightedH1Gradient_distributionally_curlFree

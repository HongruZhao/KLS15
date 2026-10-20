import KLSConstantImprovement.ActualSourceLocalizedGaffney405
import KLSConstantImprovement.ActualVectorCutoffYoung405

/-! First establish the global Jacobian domain by a fixed-ellipticity
absorption estimate. No global Jacobian norm or vanished boundary error
is an input to this estimate. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal RealInnerProductSpace Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceGaffneyAbsorption405
open KLS ActualBoundedCanonicalSource ActualSourceLocalizedGaffney405
open ActualVectorCutoffYoung405 ActualCompactWeakSourceVectorSquare
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

def sourceVectorValueSquare (u : Fin n → Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i : Fin n, u i x ^ 2

def sourceVectorJacobianSquare (Du : Fin n → Fin n → Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, Du i j x ^ 2

theorem source_vector_value_square_integrable (d : SourceData μ)
    (u : Fin n → Space n → ℝ) (hu : ∀ i, MemLp (u i) 2 (potentialMeasure d.potential)) :
    Integrable (sourceVectorValueSquare u) (potentialMeasure d.potential) := by
  apply integrable_finsetSum Finset.univ
  intro i _
  have hm := (hu i).integrable_mul (hu i)
  change Integrable (fun x => u i x * u i x) (potentialMeasure d.potential) at hm
  simpa only [pow_two] using hm

theorem source_vector_cutoff_jacobian_square_integrable (d : SourceData μ)
    (u : Fin n → Space n → ℝ) (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i, MemLp (u i) 2 (potentialMeasure d.potential))
    (hDu : ∀ i j E, IsCompact E → MemLp (Du i j) 2 (volume.restrict E))
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) :
    Integrable (fun x => χ x ^ 2 * sourceVectorJacobianSquare Du x) (potentialMeasure d.potential) := by
  have hχDu := (source_vector_cutoff_products_memLp d u Du hu hDu hχ hc).1
  have hi : Integrable (fun x => ∑ i : Fin n, ∑ j : Fin n,
      (χ x * Du i j x) * (χ x * Du i j x)) (potentialMeasure d.potential) :=
    integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => (hχDu i j).integrable_mul (hχDu i j)))
  apply hi.congr
  exact Eventually.of_forall fun x => by
    simp only [sourceVectorJacobianSquare, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Fixed-parameter coercivity absorbs the raw Jacobian boundary term.
The dependence on lambda is used only to establish the global domain. -/
theorem integral_source_vector_cutoff_jacobian_bound (d : SourceData μ)
    (u : Fin n → Space n → ℝ) (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i, MemLp (u i) 2 (potentialMeasure d.potential))
    (hDu : ∀ i j E, IsCompact E → MemLp (Du i j) 2 (volume.restrict E))
    (hw : ∀ i j, HasLocalWeakCoordinateDerivative (u i) (Du i j) j)
    (g : Space n → ℝ) (hg : MemLp g 2 (potentialMeasure d.potential))
    (hadj : rawWeakSourceVectorAdjoint d.potential u Du =ᵐ[potentialMeasure d.potential] g)
    {ell B : ℝ} (hell : 0 < ell)
    (hcoercive : ∀ᵐ x ∂potentialMeasure d.potential,
      ell * sourceVectorJacobianSquare Du x ≤ sourceVectorJacobianEnergy Du x)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (hχb : ∀ x, χ x ^ 2 ≤ 1)
    (hgrad : ∀ x, (∑ j : Fin n, coordinateDerivative χ j x ^ 2) ≤ B ^ 2) :
    (ell ^ 2 / 2) * (∫ x, χ x ^ 2 * sourceVectorJacobianSquare Du x ∂potentialMeasure d.potential) ≤
      2 * ell * (∫ x, g x ^ 2 ∂potentialMeasure d.potential) +
        (ell + 2) * B ^ 2 * (∫ x, sourceVectorValueSquare u x ∂potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let ν := potentialMeasure d.potential
  let S := fun x => χ x ^ 2 * sourceVectorJacobianSquare Du x
  let E := fun x => χ x ^ 2 * (sourceVectorMass d.potential u x + sourceVectorJacobianEnergy Du x)
  let F := fun x => χ x ^ 2 * g x ^ 2
  let Z := fun x => ∑ j : Fin n, coordinateDerivative χ j x ^ 2
  let Y := fun x => Z x * sourceVectorValueSquare u x
  let b := sourceVectorCutoffDot χ u
  let C := fun x => χ x * sourceVectorCutoffCross χ u Du x
  have hS : Integrable S ν := source_vector_cutoff_jacobian_square_integrable d u Du hu hDu hχ hc
  obtain ⟨hE, hC, _⟩ := source_vector_cutoff_energy_integrable d u Du hu hDu hχ hc
  have hb := (source_vector_cutoff_products_memLp d u Du hu hDu hχ hc).2.2
  have hχtop : MemLp χ ∞ ν := hχ.continuous.memLp_of_hasCompactSupport hc
  have hχg : MemLp (fun x => χ x * g x) 2 ν := hχtop.mul hg
  have hF : Integrable F ν := by
    have hm := hχg.integrable_mul hχg
    apply hm.congr
    exact Eventually.of_forall fun x => by
      change (χ x * g x) * (χ x * g x) = χ x ^ 2 * g x ^ 2
      ring
  have hgb : Integrable (fun x => χ x * g x * b x) ν := hχg.integrable_mul hb
  have hg2 : Integrable (fun x => g x ^ 2) ν := by
    have hm := hg.integrable_mul hg
    change Integrable (fun x => g x * g x) ν at hm
    simpa only [pow_two] using hm
  have hU : Integrable (sourceVectorValueSquare u) ν := source_vector_value_square_integrable d u hu
  have hZnonneg (x : Space n) : 0 ≤ Z x :=
    Finset.sum_nonneg (fun j _ => sq_nonneg (coordinateDerivative χ j x))
  have hZcont : Continuous Z := by
    apply continuous_finset_sum
    intro j _
    exact (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) j).continuous.pow 2
  have hY : Integrable Y ν := hU.bdd_mul hZcont.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (hZnonneg x)]; exact hgrad x)
  have hMnonneg : ∀ᵐ x ∂ν, 0 ≤ sourceVectorMass d.potential u x := by
    filter_upwards [d.hessian_ae_source] with x hx
    have hp := hx.1.posSemidef.dotProduct_mulVec_nonneg (fun i => u i x)
    have he : (fun i => u i x) ⬝ᵥ (coordinateHessian d.potential x *ᵥ (fun i => u i x)) =
        sourceVectorMass d.potential u x := by
      simp only [dotProduct, Matrix.mulVec, sourceVectorMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    simpa only [star_trivial, he] using hp
  have hlow : ell * (∫ x, S x ∂ν) ≤ ∫ x, E x ∂ν := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hS.const_mul ell) hE
    filter_upwards [hMnonneg, hcoercive] with x hm hq
    change ell * (χ x ^ 2 * sourceVectorJacobianSquare Du x) ≤
      χ x ^ 2 * (sourceVectorMass d.potential u x + sourceVectorJacobianEnergy Du x)
    have hh := mul_le_mul_of_nonneg_left hq (sq_nonneg (χ x))
    nlinarith [mul_nonneg (sq_nonneg (χ x)) hm]
  have hyoung : ell * (-2 * (∫ x, χ x * g x * b x ∂ν) - 2 * (∫ x, C x ∂ν)) ≤
      ell * (∫ x, F x ∂ν) + (ell + 2) * (∫ x, Y x ∂ν) +
        (ell ^ 2 / 2) * (∫ x, S x ∂ν) := by
    have hL1 : Integrable (fun x => -2 * (χ x * g x * b x)) ν := hgb.const_mul (-2)
    have hL2 : Integrable (fun x => 2 * C x) ν := hC.const_mul 2
    have hL0 : Integrable (fun x => -2 * (χ x * g x * b x) - 2 * C x) ν := hL1.sub hL2
    have hL : Integrable (fun x => ell * (-2 * (χ x * g x * b x) - 2 * C x)) ν := hL0.const_mul ell
    have hR1 : Integrable (fun x => ell * F x) ν := hF.const_mul ell
    have hR2 : Integrable (fun x => (ell + 2) * Y x) ν := hY.const_mul (ell + 2)
    have hR3 : Integrable (fun x => (ell ^ 2 / 2) * S x) ν := hS.const_mul (ell ^ 2 / 2)
    have hR0 : Integrable (fun x => ell * F x + (ell + 2) * Y x) ν := hR1.add hR2
    have hR : Integrable (fun x => ell * F x + (ell + 2) * Y x + (ell ^ 2 / 2) * S x) ν := hR0.add hR3
    have hp := integral_mono hL hR (fun x => by
      simpa only [S, F, E, Y, Z, b, C, sourceVectorValueSquare, sourceVectorJacobianSquare,
        sourceVectorCutoffDot, sourceVectorCutoffCross, mul_assoc] using
        vector_cutoff_signed_error_young (fun i j => Du i j x)
          (fun i => u i x) (fun i => coordinateDerivative χ i x) (χ x) (g x) hell.le)
    rw [integral_const_mul, integral_sub hL1 hL2, integral_const_mul, integral_const_mul] at hp
    rw [integral_add hR0 hR3, integral_add hR1 hR2, integral_const_mul,
      integral_const_mul, integral_const_mul] at hp
    exact hp
  have hbalance := integral_source_vector_localized_gaffney d u Du hu hDu hw g hg hadj hχ hc
  change (∫ x, E x ∂ν) = (∫ x, F x ∂ν) -
    2 * (∫ x, χ x * g x * b x ∂ν) - 2 * (∫ x, C x ∂ν) at hbalance
  have hFlower : (∫ x, F x ∂ν) ≤ ∫ x, g x ^ 2 ∂ν :=
    integral_mono hF hg2 (fun x => mul_le_of_le_one_left (sq_nonneg (g x)) (hχb x))
  have hYupper : (∫ x, Y x ∂ν) ≤ B ^ 2 * ∫ x, sourceVectorValueSquare u x ∂ν := by
    rw [← integral_const_mul]
    apply integral_mono hY (hU.const_mul (B ^ 2))
    intro x
    exact mul_le_mul_of_nonneg_right (hgrad x)
      (Finset.sum_nonneg (fun i _ => sq_nonneg (u i x)))
  have hbalanceell := congrArg (fun t : ℝ => ell * t) hbalance
  have hlowell := mul_le_mul_of_nonneg_left hlow hell.le
  have hfell := mul_le_mul_of_nonneg_left hFlower (by positivity : 0 ≤ 2 * ell)
  have hyell := mul_le_mul_of_nonneg_left hYupper (by linarith : 0 ≤ ell + 2)
  nlinarith only [hbalanceell, hyoung, hlowell, hfell, hyell]

end KLSConstantImprovement.ActualSourceGaffneyAbsorption405
#print axioms KLSConstantImprovement.ActualSourceGaffneyAbsorption405.source_vector_value_square_integrable
#print axioms KLSConstantImprovement.ActualSourceGaffneyAbsorption405.source_vector_cutoff_jacobian_square_integrable
#print axioms KLSConstantImprovement.ActualSourceGaffneyAbsorption405.integral_source_vector_cutoff_jacobian_bound

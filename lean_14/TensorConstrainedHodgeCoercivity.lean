import TensorConstrainedHodgeCore

/-! The compact physical constrained-Hodge lower bound, proved from
literal weighted derivatives and the pointwise constrained curvature. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory InnerProductSpace Set Matrix Filter
open scoped ContDiff BigOperators RealInnerProductSpace Topology
namespace KLS.DeterministicBridgeIntegration
variable {n r : ℕ} {φ : Space n → ℝ}

lemma finite_sum_four_swap_blocks {ι ρ σ τ : Type*}
    [Fintype ι] [Fintype ρ] [Fintype σ] [Fintype τ]
    (f : ι → ρ → σ → τ → ℝ) :
    (∑ i, ∑ j, ∑ a, ∑ k, f i j a k) = ∑ a, ∑ k, ∑ i, ∑ j, f i j a k := by
  calc
    _ = ∑ i, ∑ a, ∑ j, ∑ k, f i j a k := Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ a, ∑ i, ∑ j, ∑ k, f i j a k := Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ k, ∑ j, f i j a k :=
      Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun i _ => Finset.sum_comm))
    _ = _ := Finset.sum_congr rfl (fun a _ => Finset.sum_comm)

lemma tensorTwoFormGradientEnergy_eq_family
    (f : TensorTwoFormIndex n (r + 1) → Space n → ℝ) :
    tensorTwoFormGradientEnergy φ f =
      ∑ i : Fin n, ∑ j : Fin n, tensorAuxiliaryGradientEnergy φ (fun I => f (I, i, j)) := by
  unfold tensorTwoFormGradientEnergy twoFormGradientEnergy tensorAuxiliaryGradientEnergy
  exact (finite_sum_four_swap_blocks _).symm

lemma integrable_tensorAuxiliaryCurvatureForm
    (hφ : ContDiff ℝ 2 φ) {F : OrderedTensorIndex n (r + 1) → Space n → ℝ}
    (hf : ∀ I, Continuous (F I)) (hc : ∀ I, HasCompactSupport (F I)) :
    Integrable (fun x => tensorAuxiliaryCurvatureForm (coordinateHessian φ x) (fun I => F I x))
      (potentialMeasure φ) := by
  unfold tensorAuxiliaryCurvatureForm
  apply integrable_finsetSum Finset.univ
  intro I _
  apply integrable_finsetSum Finset.univ
  intro k _
  apply integrable_finsetSum Finset.univ
  intro j _
  exact integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
    ((((contDiff_coordinateHessian hφ (m := 0) (by norm_num) (I k) j).continuous).mul
      (hf I)).mul (hf _)) (hc I).mul_left.mul_right

lemma integrable_tensorTwoFormAuxiliaryCurvatureForm
    (hφ : ContDiff ℝ 2 φ) {f : TensorTwoFormIndex n (r + 1) → Space n → ℝ}
    (hf : ∀ z, Continuous (f z)) (hc : ∀ z, HasCompactSupport (f z)) :
    Integrable (fun x => tensorTwoFormAuxiliaryCurvatureForm (coordinateHessian φ x)
      (fun z => f z x)) (potentialMeasure φ) := by
  unfold tensorTwoFormAuxiliaryCurvatureForm
  exact integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
    (fun j _ => integrable_tensorAuxiliaryCurvatureForm hφ (fun I => hf _) (fun I => hc _)))

lemma integral_tensorTwoFormAuxiliaryCurvatureForm
    (hφ : ContDiff ℝ 2 φ) {f : TensorTwoFormIndex n (r + 1) → Space n → ℝ}
    (hf : ∀ z, Continuous (f z)) (hc : ∀ z, HasCompactSupport (f z)) :
    (∫ x, tensorTwoFormAuxiliaryCurvatureForm (coordinateHessian φ x) (fun z => f z x)
      ∂potentialMeasure φ) =
      ∑ i : Fin n, ∑ j : Fin n, ∫ x,
        tensorAuxiliaryCurvatureForm (coordinateHessian φ x) (fun I => f (I, i, j) x)
          ∂potentialMeasure φ := by
  unfold tensorTwoFormAuxiliaryCurvatureForm
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
    (fun j _ => integrable_tensorAuxiliaryCurvatureForm hφ (fun I => hf _) (fun I => hc _)))]
  exact Finset.sum_congr rfl (fun i _ => integral_finsetSum Finset.univ
    (fun j _ => integrable_tensorAuxiliaryCurvatureForm hφ (fun I => hf _) (fun I => hc _)))

lemma integrable_tensorTwoFormExteriorCurvatureForm
    (hφ : ContDiff ℝ 2 φ) {f : TensorTwoFormIndex n (r + 1) → Space n → ℝ}
    (hf : ∀ z, Continuous (f z)) (hc : ∀ z, HasCompactSupport (f z)) :
    Integrable (fun x => tensorTwoFormExteriorCurvatureForm (coordinateHessian φ x)
      (fun z => f z x)) (potentialMeasure φ) := by
  unfold tensorTwoFormExteriorCurvatureForm
  apply Integrable.const_mul
  apply integrable_finsetSum Finset.univ
  intro I _
  apply integrable_finsetSum Finset.univ
  intro i _
  apply integrable_finsetSum Finset.univ
  intro j _
  apply integrable_finsetSum Finset.univ
  intro k _
  exact integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
    ((((contDiff_coordinateHessian hφ (m := 0) (by norm_num) i j).continuous).mul
      (hf _)).mul (hf _)) (hc _).mul_left.mul_right

lemma integral_tensorTwoFormExteriorCurvatureForm
    (hφ : ContDiff ℝ 2 φ) {f : TensorTwoFormIndex n (r + 1) → Space n → ℝ}
    (hf : ∀ z, Continuous (f z)) (hc : ∀ z, HasCompactSupport (f z)) :
    (∫ x, tensorTwoFormExteriorCurvatureForm (coordinateHessian φ x) (fun z => f z x)
      ∂potentialMeasure φ) =
      ∑ I : OrderedTensorIndex n (r + 1), twoFormCurvatureEnergy φ (fun i j => f (I, i, j)) := by
  have hint (I : OrderedTensorIndex n (r + 1)) (i j k : Fin n) :
      Integrable (fun x => coordinateHessian φ x i j * f (I, i, k) x * f (I, j, k) x)
        (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((((contDiff_coordinateHessian hφ (m := 0) (by norm_num) i j).continuous).mul
        (hf _)).mul (hf _)) (hc _).mul_left.mul_right
  unfold tensorTwoFormExteriorCurvatureForm
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun I _ =>
    integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
      (fun j _ => integrable_finsetSum Finset.univ (fun k _ => hint I i j k))))]
  simp_rw [integral_finite_triple_sum (hint _)]
  simp only [twoFormCurvatureEnergy, Finset.mul_sum]

lemma integral_tensorTwoFormCurvatureCorrection
    (hφ : ContDiff ℝ 2 φ) {f : TensorTwoFormIndex n (r + 1) → Space n → ℝ}
    (hf : ∀ z, Continuous (f z)) (hc : ∀ z, HasCompactSupport (f z)) :
    (∫ x, tensorTwoFormCurvatureCorrection (coordinateHessian φ x) (fun z => f z x)
      ∂potentialMeasure φ) =
      (∑ I : OrderedTensorIndex n (r + 1), twoFormCurvatureEnergy φ (fun i j => f (I, i, j))) -
      (1 / (r + 2 : ℕ)) * (∫ x, tensorTwoFormAuxiliaryCurvatureForm (coordinateHessian φ x)
        (fun z => f z x) ∂potentialMeasure φ) := by
  unfold tensorTwoFormCurvatureCorrection
  rw [integral_sub (integrable_tensorTwoFormExteriorCurvatureForm hφ hf hc)
    ((integrable_tensorTwoFormAuxiliaryCurvatureForm hφ hf hc).const_mul _),
    integral_const_mul, integral_tensorTwoFormExteriorCurvatureForm hφ hf hc]

lemma tensorTwoFormContractionEnergy_le
    (hφ : ContDiff ℝ 2 φ) {f : TensorTwoFormIndex n (r + 1) → Space n → ℝ}
    (hf : ∀ z, ContDiff ℝ 2 (f z)) (hc : ∀ z, HasCompactSupport (f z))
    (hF : ∀ x, TensorTwoFormCompatible (fun z => f z x)) :
    tensorTwoFormContractionEnergy φ f ≤ (r + 1 : ℕ) * tensorTwoFormGradientEnergy φ f +
      ∫ x, tensorTwoFormAuxiliaryCurvatureForm (coordinateHessian φ x) (fun z => f z x)
        ∂potentialMeasure φ := by
  have h := tensorAuxiliaryContractionEnergy_family_le (τ := Fin n × Fin n) hφ
    (F := fun a I => f (I, a.1, a.2)) (fun a I => hf _) (fun a I => hc _)
    (fun a I J hp => funext fun x => (hF x).1 I J hp a.1 a.2)
  rw [tensorTwoFormGradientEnergy_eq_family,
    integral_tensorTwoFormAuxiliaryCurvatureForm hφ (fun z => (hf z).continuous) hc]
  simpa only [tensorTwoFormContractionEnergy, Fintype.sum_prod_type] using h

/-- The actual compact constrained weighted Hodge inequality (5.7).
The gradient coefficient is 1/(q+1), q=r+1; the remainder is the literal
curvature correction, with no domain or density assumption. -/
theorem tensorConstrainedHodgeEnergy_lower_gradient_curvature
    (hφ : ContDiff ℝ 2 φ) {f : TensorTwoFormIndex n (r + 1) → Space n → ℝ}
    (hf : ∀ z, ContDiff ℝ 2 (f z)) (hc : ∀ z, HasCompactSupport (f z))
    (hF : ∀ x, TensorTwoFormCompatible (fun z => f z x)) :
    (1 / (r + 2 : ℕ)) * tensorTwoFormGradientEnergy φ f +
      (∫ x, tensorTwoFormCurvatureCorrection (coordinateHessian φ x) (fun z => f z x)
        ∂potentialMeasure φ) ≤ tensorConstrainedHodgeEnergy φ f := by
  have hid := tensorConstrainedHodgeEnergy_identity hφ hf hc hF
  have hup := tensorTwoFormContractionEnergy_le hφ hf hc hF
  rw [integral_tensorTwoFormCurvatureCorrection hφ (fun z => (hf z).continuous) hc]
  have hm : (0 : ℝ) < (r + 2 : ℕ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hup (le_of_lt (one_div_pos.mpr hm))
  have hcst : (1 / (r + 2 : ℕ) : ℝ) * (r + 1 : ℕ) = 1 - 1 / (r + 2 : ℕ) := by
    push_cast
    field_simp
    ring
  rw [mul_add, ← mul_assoc, hcst] at hscaled
  linarith

lemma integrable_tensorTwoFormNormSq (hφ : Continuous φ)
    {f : TensorTwoFormIndex n (r + 1) → Space n → ℝ}
    (hf : ∀ z, Continuous (f z)) (hc : ∀ z, HasCompactSupport (f z)) :
    Integrable (fun x => tensorTwoFormNormSq (fun z => f z x)) (potentialMeasure φ) := by
  unfold tensorTwoFormNormSq
  exact integrable_finsetSum Finset.univ (fun I _ => integrable_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ
      (fun j _ => compact_coefficient_square_integrable hφ (hf _) (hc _))))

/-- Strong coercivity of the literal compact constrained Hodge form.
Only the actual pointwise Hessian lower bound is assumed; the constrained
curvature estimate and all analytic integration identities are proved. -/
theorem tensorConstrainedHodgeEnergy_coercive
    (hφ : ContDiff ℝ 2 φ) {f : TensorTwoFormIndex n (r + 1) → Space n → ℝ}
    (hf : ∀ z, ContDiff ℝ 2 (f z)) (hc : ∀ z, HasCompactSupport (f z))
    (hF : ∀ x, TensorTwoFormCompatible (fun z => f z x)) {a : ℝ}
    (hlower : ∀ (x : Space n) (v : Fin n → ℝ),
      a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ x *ᵥ v)) :
    (1 / (r + 2 : ℕ)) * tensorTwoFormGradientEnergy φ f +
      ((r + 3 : ℕ) / (r + 2 : ℕ) : ℝ) * a *
        (∫ x, tensorTwoFormNormSq (fun z => f z x) ∂potentialMeasure φ) ≤
      tensorConstrainedHodgeEnergy φ f := by
  have hb := tensorConstrainedHodgeEnergy_lower_gradient_curvature hφ hf hc hF
  have hint : (((r + 3 : ℕ) / (r + 2 : ℕ) : ℝ) * a) *
      (∫ x, tensorTwoFormNormSq (fun z => f z x) ∂potentialMeasure φ) ≤
      ∫ x, tensorTwoFormCurvatureCorrection (coordinateHessian φ x) (fun z => f z x)
        ∂potentialMeasure φ := by
    rw [← integral_const_mul]
    apply integral_mono
    · exact (integrable_tensorTwoFormNormSq hφ.continuous (fun z => (hf z).continuous) hc).const_mul _
    · exact (integrable_tensorTwoFormExteriorCurvatureForm hφ (fun z => (hf z).continuous) hc).sub
        ((integrable_tensorTwoFormAuxiliaryCurvatureForm hφ (fun z => (hf z).continuous) hc).const_mul _)
    · intro x
      exact tensorTwoFormCurvatureCorrection_lower (coordinateHessian φ x)
        (coordinateHessian_symmetric hφ x) (fun z => f z x) (hF x) (hlower x)
  linarith

end KLS.DeterministicBridgeIntegration
end

#print axioms KLS.DeterministicBridgeIntegration.tensorConstrainedHodgeEnergy_lower_gradient_curvature
#print axioms KLS.DeterministicBridgeIntegration.tensorConstrainedHodgeEnergy_coercive

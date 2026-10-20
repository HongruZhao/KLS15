import ActualKLS14452512512Endpoints
import KLS15Improvements

/-! Combine the imported creation/correlated-observation/projection proof with
the exact affine Schur completion and the actual product-exponential results.
The universal endpoint is 14.452512512; the product compact C1 endpoint is 4.
No smaller universal constant is asserted by this integration. -/
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff ENNReal NNReal
namespace KLSImprovement.Combined14452512512
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSImprovement.ActualAffineSchur KLSImprovement.ActualSchurEndpoint
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def bound : ℝ := 56455127 / 3906250

/-- The imported quantitative improvement feeds the existing exact Schur
criterion on the actual compatible tensor carriers. -/
theorem regularPoincareCombined
    {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hn : 0 < n) (hμ : admissibleMeasure (potentialMeasure φ)) :
    poincareConstant (potentialMeasure φ) ≤ ENNReal.ofReal bound := by
  apply poincareConstant_le_of_actual_joint_schur hφ hκ hlower hn hμ.isotropic
    (by norm_num [bound])
  apply actual_joint_schur_of_graded_norm_bound hφ hκ hlower hμ.isotropic
    (by norm_num [bound])
  have hb := actual_projection_three_head_refined_operator_norm_sq_le hφ hκ hlower hμ
  have he := KLSBelow25.ProjectionThreeHeadRefinedNumerics.endpoint_value
  change 1 + ‖gradedTensorIntegration hφ hκ hlower‖ ^ 2 ≤ 56455127 / 3906250
  linarith

theorem poincareCombined_mem {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    (56455127 / 3906250 : ℝ≥0) ∈ poincareConstants μ := by
  apply mem_poincareConstants_of_paperRegularDensity hμ (by norm_num)
  intro ν hν hregular
  obtain ⟨V, κ, hV, hκ, hstrong, hupper, hgrowth, heq⟩ := hregular
  subst ν
  let : IsProbabilityMeasure (potentialMeasure V) := hν.isProb
  let hlower := coordinateHessian_lower_of_strongConvexOn (hV.of_le (by simp)) hstrong
  have hc := regularPoincareCombined hV hκ hlower (by omega) hν
  have hfin : poincareConstant (potentialMeasure V) < ⊤ := hc.trans_lt ENNReal.ofReal_lt_top
  apply (poincareConstants_iff_optimal_le (poincareConstants_nonempty_iff.mpr hfin)
    (hν.poincareConstant_pos hn)).mpr
  convert hc using 1
  unfold bound
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3906250)]
  norm_num

theorem poincareCombined {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : LocallyLipschitzTests μ f) :
    variance μ f ≤ (56455127 / 3906250 : ℝ≥0∞) * energy μ f := by
  simpa using poincareCombined_mem hn hμ f hf

theorem universalPoincareUpperCombined :
    universalPoincareConstant ≤ (56455127 / 3906250 : ℝ≥0∞) := by
  apply universal_le_iff.mpr
  intro n hn μ hμ
  simpa using poincareConstant_le_of_mem (poincareCombined_mem hn hμ)

theorem openaiPoincareCombined {n : ℕ} (hn : 1 ≤ n)
    {ρ : OAI.LeanBlast.KLS.Space n → ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (hiso : OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ)
      ((56455127 : ℝ) / 3906250) :=
  OpenAIBridge.poincareBound_of_mem hρ
    (poincareCombined_mem hn (OpenAIBridge.admissible hρ hiso))

/-- The actual centered product exponential retains its sharper endpoint. -/
theorem product_benchmark_covariance_charge (n : ℕ)
    (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ProbabilityTheory.variance f (KLSImprovement.Tensorization.centeredProductLaw n) +
      (1 / 3 : ℝ) * (∑ i, (∫ x, x i * f x
        ∂KLSImprovement.Tensorization.centeredProductLaw n) ^ 2) ≤
      4 * (∫ x, ∑ i, (KLSImprovement.Tensorization.coordinateDeriv f i x) ^ 2
        ∂KLSImprovement.Tensorization.centeredProductLaw n) :=
  KLSImprovement.Tensorization.centered_exponential_product_covariance_charge n f hf hc

/-- The imported flat cubic cap is still 239/60 times the sharp product cap. -/
theorem cubic_flat_cap_ratio : KLSBelow25.CreationSeed239.B / 6 = (239 / 60 : ℝ) := by
  norm_num [KLSBelow25.CreationSeed239.B]

end KLSImprovement.Combined14452512512
#print axioms KLSImprovement.Combined14452512512.regularPoincareCombined
#print axioms KLSImprovement.Combined14452512512.poincareCombined_mem
#print axioms KLSImprovement.Combined14452512512.poincareCombined
#print axioms KLSImprovement.Combined14452512512.universalPoincareUpperCombined
#print axioms KLSImprovement.Combined14452512512.openaiPoincareCombined
#print axioms KLSImprovement.Combined14452512512.product_benchmark_covariance_charge
#print axioms KLSImprovement.Combined14452512512.cubic_flat_cap_ratio

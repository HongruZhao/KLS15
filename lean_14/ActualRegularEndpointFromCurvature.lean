import ActualAppellCoefficientInduction
import ActualCoefficientObservationBounds
import PaperRegularApproximation
import OpenAIKLSBridge

/-! All genuine Appell coefficient and observation hypotheses are discharged.
Only the actual tensor-curvature comparison remains in the regular endpoint.
The full-class and upstream endpoints below explicitly retain that gate. -/
noncomputable section
open MeasureTheory Matrix Set
open scoped ContDiff ENNReal NNReal
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ),
    κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

theorem actual_regular_poincare_twentyFour886_of_curvature
    (hn : 0 < n) (hμ : admissibleMeasure (potentialMeasure φ))
    (hcomparison : ActualTensorCurvatureComparison hφ hκ hlower) :
    poincareConstant (potentialMeasure φ) ≤ ENNReal.ofReal (12443/500 : ℝ) := by
  apply actual_regular_poincare_twentyFour886_of_coefficient_and_curvature
    hφ hκ hlower hn hμ hcomparison
  intro j f
  have hb := actualAppellEnergy_coefficientH_bound (by omega : 1 ≤ j+3) hμ (Lp.memLp f)
  rwa [←actualLp_norm_sq_eq_integral] at hb

theorem actual_regular_poincare_twentyFive_of_curvature
    (hn : 0 < n) (hμ : admissibleMeasure (potentialMeasure φ))
    (hcomparison : ActualTensorCurvatureComparison hφ hκ hlower) :
    poincareConstant (potentialMeasure φ) ≤ ENNReal.ofReal 25 :=
  (actual_regular_poincare_twentyFour886_of_curvature hφ hκ hlower hn hμ hcomparison).trans
    (ENNReal.ofReal_le_ofReal (by norm_num))

def PaperRegularTensorCurvatureGate : Prop :=
  ∀ (n : ℕ) (V : Space n → ℝ) (κ : ℝ) [IsProbabilityMeasure (potentialMeasure V)]
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hκ : 0 < κ)
    (hstrong : StrongConvexOn univ κ V),
    HasHessianUpperBound V → HasPolynomialDerivativeGrowth V →
    admissibleMeasure (potentialMeasure V) →
    ActualTensorCurvatureComparison hV hκ
      (coordinateHessian_lower_of_strongConvexOn (hV.of_le (by simp)) hstrong)

theorem actual_full_poincare_twentyFour886_of_regular_curvature
    (hgate : PaperRegularTensorCurvatureGate) {n : ℕ} (hn : 1 ≤ n)
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ) :
    (12443/500 : ℝ≥0) ∈ poincareConstants μ := by
  apply mem_poincareConstants_of_paperRegularDensity hμ (by norm_num)
  intro ν hν hregular
  obtain ⟨V,κ,hV,hκ,hstrong,hupper,hgrowth,heq⟩ := hregular
  subst ν
  let : IsProbabilityMeasure (potentialMeasure V) := hν.isProb
  let hlower := coordinateHessian_lower_of_strongConvexOn (hV.of_le (by simp)) hstrong
  have hc := actual_regular_poincare_twentyFour886_of_curvature hV hκ hlower
    (by omega) hν (hgate n V κ hV hκ hstrong hupper hgrowth hν)
  have hfin : poincareConstant (potentialMeasure V) < ⊤ := hc.trans_lt ENNReal.ofReal_lt_top
  apply (poincareConstants_iff_optimal_le (poincareConstants_nonempty_iff.mpr hfin)
    (hν.poincareConstant_pos hn)).mpr
  convert hc using 1
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 500)]
  norm_num

theorem actual_universal_twentyFour886_of_regular_curvature
    (hgate : PaperRegularTensorCurvatureGate) :
    universalPoincareConstant ≤ (12443/500 : ℝ≥0∞) := by
  apply universal_le_iff.mpr
  intro n hn μ hμ
  simpa using poincareConstant_le_of_mem
    (actual_full_poincare_twentyFour886_of_regular_curvature hgate hn hμ)

theorem actual_universal_twentyFive_of_regular_curvature
    (hgate : PaperRegularTensorCurvatureGate) :
    universalPoincareConstant ≤ 25 :=
  (actual_universal_twentyFour886_of_regular_curvature hgate).trans (by
    rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]
    norm_num)

theorem actual_openai_twentyFour886_of_regular_curvature
    (hgate : PaperRegularTensorCurvatureGate) {n : ℕ} (hn : 1 ≤ n)
    {ρ : OAI.LeanBlast.KLS.Space n → ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (hiso : OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ)
      (12443/500 : ℝ) := by
  exact OpenAIBridge.poincareBound_of_mem hρ
    (actual_full_poincare_twentyFour886_of_regular_curvature hgate hn (OpenAIBridge.admissible hρ hiso))

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_regular_poincare_twentyFour886_of_curvature
#print axioms KLS.DeterministicBridgeNext.actual_full_poincare_twentyFour886_of_regular_curvature
#print axioms KLS.DeterministicBridgeNext.actual_universal_twentyFive_of_regular_curvature
#print axioms KLS.DeterministicBridgeNext.actual_openai_twentyFour886_of_regular_curvature
